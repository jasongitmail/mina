open Core
open Currency
open Mina_base
open Signature_lib
module Impl = Pickles.Impls.Step
module Inner_curve = Snark_params.Tick.Inner_curve
module Nat = Pickles_types.Nat
module Local_state = Mina_state.Local_state
module Parties_segment = Transaction_snark.Parties_segment
module Statement = Transaction_snark.Statement

let constraint_constants = Genesis_constants.Constraint_constants.for_unit_tests

let genesis_constants = Genesis_constants.for_unit_tests

let proof_level = Genesis_constants.Proof_level.for_unit_tests

let consensus_constants =
  Consensus.Constants.create ~constraint_constants
    ~protocol_constants:genesis_constants.protocol

(* For tests let's just monkey patch ledger and sparse ledger to freeze their
 * ledger_hashes. The nominal type is just so we don't mix this up in our
 * real code. *)
module Ledger = struct
  include Mina_base.Ledger

  let merkle_root t = Frozen_ledger_hash.of_ledger_hash @@ merkle_root t
end

module Sparse_ledger = struct
  include Mina_base.Sparse_ledger

  let merkle_root t = Frozen_ledger_hash.of_ledger_hash @@ merkle_root t
end

let ledger_depth = constraint_constants.ledger_depth

include Transaction_snark.Make (struct
  let constraint_constants = constraint_constants

  let proof_level = proof_level
end)

let state_body =
  let compile_time_genesis =
    (*not using Precomputed_values.for_unit_test because of dependency cycle*)
    Mina_state.Genesis_protocol_state.t
      ~genesis_ledger:Genesis_ledger.(Packed.t for_unit_tests)
      ~genesis_epoch_data:Consensus.Genesis_epoch_data.for_unit_tests
      ~constraint_constants ~consensus_constants
  in
  compile_time_genesis.data |> Mina_state.Protocol_state.body

open Snark_params.Tick
open Snark_params.Tick.Let_syntax

type _witness = Schnorr.Signature.t

(* check a signature on msg against a public key *)
let check_sig pk msg sigma : (Boolean.var, _) Checked.t =
  let%bind (module S) = Inner_curve.Checked.Shifted.create () in
  Schnorr.Checked.verifies (module S) sigma pk msg

(* verify witness signature against public keys *)
let%snarkydef verify_sig pubkeys msg sigma =
  let%bind pubkeys =
    exists
      (Typ.list ~length:(List.length pubkeys) Inner_curve.typ)
      ~compute:(As_prover.return pubkeys)
  in
  Checked.List.exists pubkeys ~f:(fun pk -> check_sig pk msg sigma)
  >>= Boolean.Assert.is_true

let check_witness pubkeys msg witness =
  Transaction_snark.dummy_constraints ()
  >>= fun () -> verify_sig pubkeys msg witness

let%test_unit "1-of-1" =
  let gen =
    let open Quickcheck.Generator.Let_syntax in
    let%map sk = Private_key.gen and msg = Field.gen_uniform in
    (sk, Random_oracle.Input.field_elements [| msg |])
  in
  Quickcheck.test ~trials:1 gen ~f:(fun (sk, msg) ->
      let pk = Inner_curve.(scale one sk) in
      (let sigma = Schnorr.sign sk msg in
       let%bind sigma_var =
         exists Schnorr.Signature.typ ~compute:(As_prover.return sigma)
       in
       let%bind msg_var =
         exists (Schnorr.message_typ ()) ~compute:(As_prover.return msg)
       in
       check_witness [ pk ] msg_var sigma_var)
      |> Checked.map ~f:As_prover.return
      |> Fn.flip run_and_check () |> Or_error.ok_exn |> snd)

let%test_unit "1-of-2" =
  let gen =
    let open Quickcheck.Generator.Let_syntax in
    let%map sk0 = Private_key.gen
    and sk1 = Private_key.gen
    and msg = Field.gen_uniform in
    (sk0, sk1, Random_oracle.Input.field_elements [| msg |])
  in
  Quickcheck.test ~trials:1 gen ~f:(fun (sk0, sk1, msg) ->
      let pk0 = Inner_curve.(scale one sk0) in
      let pk1 = Inner_curve.(scale one sk1) in
      (let sigma1 = Schnorr.sign sk1 msg in
       let%bind sigma1_var =
         exists Schnorr.Signature.typ ~compute:(As_prover.return sigma1)
       and msg_var =
         exists (Schnorr.message_typ ()) ~compute:(As_prover.return msg)
       in
       check_witness [ pk0; pk1 ] msg_var sigma1_var)
      |> Checked.map ~f:As_prover.return
      |> Fn.flip run_and_check () |> Or_error.ok_exn |> snd)

type _ Snarky_backendless.Request.t +=
  | Sigma : Schnorr.Signature.t Snarky_backendless.Request.t

(* test a snapp tx with a 3-party ring *)
let%test_unit "ring-signature snapp tx with 3 parties" =
  let open Transaction_logic.For_tests in
  let gen =
    let open Quickcheck.Generator.Let_syntax in
    let%map sk0 = Private_key.gen
    and sk1 = Private_key.gen
    and sk2 = Private_key.gen
    (* index of the key that will sign the msg *)
    and sign_index = Base_quickcheck.Generator.int_inclusive 0 2
    and test_spec = Test_spec.gen in
    let secrets = (sk0, sk1, sk2) in
    (secrets, sign_index, test_spec)
  in
  Quickcheck.test ~trials:1 gen
    ~f:(fun (secrets, sign_index, { init_ledger; specs }) ->
      let sk0, sk1, sk2 = secrets in
      let pk0 = Inner_curve.(scale one sk0) in
      let pk1 = Inner_curve.(scale one sk1) in
      let pk2 = Inner_curve.(scale one sk2) in
      Ledger.with_ledger ~depth:ledger_depth ~f:(fun ledger ->
          Init_ledger.init (module Ledger.Ledger_inner) init_ledger ledger ;
          let spec = List.hd_exn specs in
          let tag, _, (module P), Pickles.Provers.[ ringsig_prover; _ ] =
            let ring_sig_rule : _ Pickles.Inductive_rule.t =
              let ring_sig_main (tx_commitment : Snapp_statement.Checked.t) :
                  (unit, _) Checked.t =
                let%bind sigma_var =
                  exists Schnorr.Signature.typ ~request:(As_prover.return Sigma)
                in
                let msg_var =
                  tx_commitment |> Snapp_statement.Checked.to_field_elements
                  |> Random_oracle_input.field_elements
                in
                check_witness [ pk0; pk1; pk2 ] msg_var sigma_var
              in
              { identifier = "ring-sig-rule"
              ; prevs = []
              ; main =
                  (fun [] x ->
                    ring_sig_main x |> Run.run_checked
                    |> fun _ :
                           unit
                           Pickles_types.Hlist0.H1
                             (Pickles_types.Hlist.E01(Pickles.Inductive_rule.B))
                           .t ->
                    [])
              ; main_value = (fun [] _ -> [])
              }
            in
            Pickles.compile ~cache:Cache_dir.cache
              (module Snapp_statement.Checked)
              (module Snapp_statement)
              ~typ:Snapp_statement.typ
              ~branches:(module Nat.N2)
              ~max_branching:(module Nat.N2) (* You have to put 2 here... *)
              ~name:"ringsig"
              ~constraint_constants:
                (Genesis_constants.Constraint_constants.to_snark_keys_header
                   constraint_constants)
              ~choices:(fun ~self ->
                [ ring_sig_rule
                ; { identifier = "dummy"
                  ; prevs = [ self; self ]
                  ; main_value = (fun [ _; _ ] _ -> [ true; true ])
                  ; main =
                      (fun [ _; _ ] _ ->
                        let dummy_constraints () =
                          let open Run in
                          let b =
                            exists Boolean.typ_unchecked ~compute:(fun _ ->
                                true)
                          in
                          let g =
                            exists Pickles.Step_main_inputs.Inner_curve.typ
                              ~compute:(fun _ ->
                                Inner_curve.(to_affine_exn one))
                          in
                          let (_ : _) =
                            Pickles.Step_main_inputs.Ops.scale_fast g
                              (`Plus_two_to_len [| b; b |])
                          in
                          let (_ : _) =
                            Pickles.Pairing_main.Scalar_challenge.endo g
                              (Scalar_challenge [ b ])
                          in
                          ()
                        in
                        dummy_constraints ()
                        |> fun () ->
                        (* Unsatisfiable. *)
                        Run.exists Field.typ ~compute:(fun () ->
                            Run.Field.Constant.zero)
                        |> fun s ->
                        Run.Field.(Assert.equal s (s + one))
                        |> fun () :
                               ( Snapp_statement.Checked.t
                               * (Snapp_statement.Checked.t * unit) )
                               Pickles_types.Hlist0.H1
                                 (Pickles_types.Hlist.E01
                                    (Pickles.Inductive_rule.B))
                               .t ->
                        [ Boolean.true_; Boolean.true_ ])
                  }
                ])
          in
          let vk = Pickles.Side_loaded.Verification_key.of_compiled tag in
          let { Transaction_logic.For_tests.Transaction_spec.fee
              ; sender = sender, sender_nonce
              ; receiver = ringsig_account_pk
              ; amount
              } =
            spec
          in
          let vk = With_hash.of_data ~hash_data:Snapp_account.digest_vk vk in
          let _show_vk =
            With_hash.to_yojson Side_loaded_verification_key.to_yojson
              (fun fe -> `String (Field.to_string fe))
              vk
            |> Yojson.Safe.to_string |> print_endline
          in
          let _show_vk =
            With_hash.data vk
            |> Binable.to_string (module Side_loaded_verification_key.Stable.V1)
            |> Base64.encode_exn ~alphabet:Base64.uri_safe_alphabet
            |> print_endline
          in
          let total = Option.value_exn (Amount.add fee amount) in
          (let _is_new, _loc =
             let pk = Public_key.compress sender.public_key in
             let id = Account_id.create pk Token_id.default in
             Ledger.get_or_create_account ledger id
               (Account.create id
                  Balance.(Option.value_exn (add_amount zero total)))
             |> Or_error.ok_exn
           in
           let _is_new, loc =
             let id = Account_id.create ringsig_account_pk Token_id.default in
             Ledger.get_or_create_account ledger id
               (Account.create id Balance.(of_int 0))
             |> Or_error.ok_exn
           in
           let a = Ledger.get ledger loc |> Option.value_exn in
           Ledger.set ledger loc
             { a with
               permissions =
                 { Permissions.user_default with set_permissions = Proof }
             ; snapp =
                 Some
                   { (Option.value ~default:Snapp_account.default a.snapp) with
                     verification_key = Some vk
                   }
             }) ;
          let update_empty_permissions =
            let permissions = Snapp_basic.Set_or_keep.Set Permissions.empty in
            { Party.Update.noop with permissions }
          in
          let fee_payer =
            { Party.Signed.data =
                { body =
                    { pk = sender.public_key |> Public_key.compress
                    ; update = Party.Update.noop
                    ; token_id = Token_id.default
                    ; delta = Amount.Signed.(negate (of_unsigned total))
                    ; events = []
                    ; rollup_events = []
                    ; call_data = Field.zero
                    ; depth = 0
                    }
                ; predicate = sender_nonce
                }
                (* Real signature added in below *)
            ; authorization = Signature.dummy
            }
          in
          let snapp_party_data : Party.Predicated.t =
            { Party.Predicated.Poly.body =
                { pk = ringsig_account_pk
                ; update = update_empty_permissions
                ; token_id = Token_id.default
                ; delta = Amount.Signed.(of_unsigned amount)
                ; events = []
                ; rollup_events = []
                ; call_data = Field.zero
                ; depth = 0
                }
            ; predicate = Full Snapp_predicate.Account.accept
            }
          in
          let protocol_state = Snapp_predicate.Protocol_state.accept in
          let ps =
            Parties.Party_or_stack.of_parties_list
              ~party_depth:(fun (p : Party.Predicated.t) -> p.body.depth)
              [ snapp_party_data ]
            |> Parties.Party_or_stack.accumulate_hashes_predicated
          in
          let other_parties_hash = Parties.Party_or_stack.stack_hash ps in
          let protocol_state_predicate_hash =
            (*FIXME: is this ok? *)
            Snapp_predicate.Protocol_state.digest protocol_state
          in
          let transaction : Parties.Transaction_commitment.t =
            (*FIXME: is this correct? *)
            Parties.Transaction_commitment.create ~other_parties_hash
              ~protocol_state_predicate_hash
          in
          let at_party = Parties.Party_or_stack.stack_hash ps in
          let tx_statement : Snapp_statement.t = { transaction; at_party } in
          let msg =
            tx_statement |> Snapp_statement.to_field_elements
            |> Random_oracle_input.field_elements
          in
          let signing_sk = List.nth_exn [ sk0; sk1; sk2 ] sign_index in
          let sigma = Schnorr.sign signing_sk msg in
          let handler (Snarky_backendless.Request.With { request; respond }) =
            match request with
            | Sigma ->
                respond @@ Provide sigma
            | _ ->
                respond Unhandled
          in
          let pi : Pickles.Side_loaded.Proof.t =
            (fun () -> ringsig_prover ~handler [] tx_statement)
            |> Async.Thread_safe.block_on_async_exn
          in
          let fee_payer =
            let txn_comm =
              Parties.Transaction_commitment.with_fee_payer transaction
                ~fee_payer_hash:
                  Party.Predicated.(digest (of_signed fee_payer.data))
            in
            { fee_payer with
              authorization =
                Signature_lib.Schnorr.sign sender.private_key
                  (Random_oracle.Input.field txn_comm)
            }
          in
          let parties : Parties.t =
            { fee_payer
            ; other_parties =
                [ { data = snapp_party_data; authorization = Proof pi } ]
            ; protocol_state
            }
          in
          let w : Parties_segment.Witness.t =
            { global_ledger =
                Sparse_ledger.of_ledger_subset_exn ledger
                  (Parties.accounts_accessed parties)
            ; local_state_init =
                { parties = []
                ; call_stack = []
                ; ledger =
                    Sparse_ledger.of_root ~depth:ledger_depth
                      ~next_available_token:Token_id.(next default)
                      Local_state.dummy.ledger
                ; transaction_commitment = transaction
                ; token_id = Token_id.default
                ; excess = Amount.zero
                ; success = true
                ; will_succeed = true
                }
            ; start_parties =
                [ { will_succeed = true
                  ; protocol_state_predicate =
                      Snapp_predicate.Protocol_state.accept
                  ; parties
                  }
                ]
            ; state_body
            }
          in
          let _, (local_state_post, excess) =
            Ledger.apply_parties_unchecked ledger ~constraint_constants
              ~state_view:(Mina_state.Protocol_state.Body.view state_body)
              parties
            |> Or_error.ok_exn
          in
          let statement : Statement.With_sok.t =
            { source =
                { ledger = Sparse_ledger.merkle_root w.global_ledger
                ; next_available_token =
                    Sparse_ledger.next_available_token w.global_ledger
                ; pending_coinbase_stack = Pending_coinbase.Stack.empty
                ; local_state =
                    { w.local_state_init with
                      parties =
                        Parties.Party_or_stack.With_hashes.stack_hash
                          w.local_state_init.parties
                    ; call_stack =
                        Parties.Party_or_stack.With_hashes.stack_hash
                          w.local_state_init.call_stack
                    ; ledger =
                        Sparse_ledger.merkle_root w.local_state_init.ledger
                    }
                }
            ; target =
                { ledger = Ledger.merkle_root ledger
                ; next_available_token = Ledger.next_available_token ledger
                ; pending_coinbase_stack = Pending_coinbase.Stack.empty
                ; local_state =
                    { local_state_post with
                      parties =
                        Parties.Party_or_stack.(
                          stack_hash
                            (accumulate_hashes' local_state_post.parties))
                    ; call_stack =
                        Parties.Party_or_stack.(
                          stack_hash
                            (accumulate_hashes' local_state_post.call_stack))
                    ; ledger = Local_state.dummy.ledger
                    ; transaction_commitment =
                        Parties.Transaction_commitment.empty
                    }
                }
            ; supply_increase = Amount.zero
            ; fee_excess =
                { fee_token_l = Token_id.default
                ; fee_excess_l = Fee.Signed.of_unsigned (Amount.to_fee excess)
                ; fee_token_r = Token_id.default
                ; fee_excess_r = Fee.Signed.zero
                }
            ; sok_digest = Sok_message.Digest.default
            }
          in
          let open Impl in
          run_and_check
            (fun () ->
              let s =
                exists Statement.With_sok.typ ~compute:(fun () -> statement)
              in
              let tx_statement =
                exists Snapp_statement.typ ~compute:(fun () -> tx_statement)
              in
              Transaction_snark.Base.Parties_snark.main ~constraint_constants
                [ { predicate_type = `Nonce_or_accept
                  ; auth_type = Signature
                  ; is_start = `Yes
                  }
                ; { predicate_type = `Full; auth_type = Proof; is_start = `No }
                ]
                [ (0, tx_statement) ] s ~witness:w ;
              fun () -> ())
            ())
      |> Or_error.ok_exn
      |> fun ((), ()) -> ())

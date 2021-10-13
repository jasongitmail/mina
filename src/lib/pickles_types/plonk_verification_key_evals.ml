open Core_kernel
module H_list = Snarky_backendless.H_list

[%%versioned
module Stable = struct
  module V1 = struct
    type 'comm t = 'comm Kimchi.Protocol.VerifierIndex.verification_evals =
      { sigma_comm : 'comm array
      ; qw_comm : 'comm array
      ; qm_comm : 'comm
      ; qc_comm : 'comm
      ; rcm_comm : 'comm array array
      ; psm_comm : 'comm
      ; add_comm : 'comm
      ; double_comm : 'comm
      ; mul_comm : 'comm
      ; emul_comm : 'comm
      }
    [@@deriving sexp, equal, compare, hash, yojson, hlist, fields]
  end
end]

let map
    { sigma_comm
    ; qw_comm
    ; qm_comm
    ; qc_comm
    ; rcm_comm
    ; psm_comm
    ; add_comm
    ; double_comm
    ; mul_comm
    ; emul_comm
    } ~f =
  { sigma_comm = Array.map ~f sigma_comm
  ; qw_comm = Array.map ~f qw_comm
  ; qm_comm = f qm_comm
  ; qc_comm = f qc_comm
  ; rcm_comm = Array.map ~f:(fun x -> Array.map ~f x) rcm_comm
  ; psm_comm = f psm_comm
  ; add_comm = f add_comm
  ; double_comm = f double_comm
  ; mul_comm = f mul_comm
  ; emul_comm = f emul_comm
  }

let map2 t1 t2 ~f = failwith "unimplemented"

(* { sigma_comm = f t1.sigma_comm t2.sigma_comm
   ; qw_comm = f t1.qw_comm t2.qw_comm
   ; qm_comm = f t1.qm_comm t2.qm_comm
   ; qc_comm = f t1.qc_comm t2.qc_comm
   ; rcm_comm = f t1.rcm_comm t2.rcm_comm
   ; psm_comm = f t1.psm_comm t2.psm_comm
   ; add_comm = f t1.add_comm t2.add_comm
   ; double_comm = f t1.double_comm t2.double_comm
   ; mul_comm = f t1.mul_comm t2.mul_comm
   ; emul_comm = f t1.emul_comm t2.emul_comm
   } *)

let typ g =
  Snarky_backendless.Typ.of_hlistable
    [ g; g; g; g; g; g; g; g; g; g; g; g; g; g; g; g; g; g ]
    ~var_to_hlist:to_hlist ~var_of_hlist:of_hlist ~value_to_hlist:to_hlist
    ~value_of_hlist:of_hlist

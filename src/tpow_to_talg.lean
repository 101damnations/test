import tpow

universe u
variables (R : Type u) [comm_semiring R] (M : Type u) [add_comm_monoid M] [semimodule R M]
open tpow

/-def talg_ring : ring (tensor_algebra R M) :=
algebra.semiring_to_ring R
def talg_acg : add_comm_group (tensor_algebra R M) :=
@ring.to_add_comm_group _ talg_ring
def talg_mod : @module R (tensor_algebra R M) _ talg_acg :=
{ smul := (•),
  one_smul := one_smul _,
  mul_smul := mul_smul,
  smul_add := smul_add,
  smul_zero := smul_zero,
  add_smul := add_smul,
  zero_smul := zero_smul _ }-/

def pow_to_alg (n : ℕ) : (tpow R M n) →ₗ[R] (tensor_algebra R M) :=
tpow.lift R n (tensor_algebra R M) $ tensor_algebra.mk R M

variables {R M}
theorem inj_of_pow_to_alg (n : ℕ) : (pow_to_alg R M n).ker = ⊥ :=
linear_map.ker_eq_bot'.2 $ λ x h, sorry

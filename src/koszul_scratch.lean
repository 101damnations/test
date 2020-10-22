
import linear_algebra.exterior_algebra  algebra.homology.resolution algebra.algebra.subalgebra linear_algebra.basis algebra.homology.chain_complex algebra.category.Module.basic
variables (R : Type*) (M : Type*)
open_locale classical tensor_product
/-
local attribute [semireducible] tensor_algebra exterior_algebra ring_quot
section
variables [comm_semiring R] [add_comm_monoid M] [semimodule R M]

def algebra_alg_hom (S : Type*) [semiring S] [algebra R S] : R →ₐ[R] S :=
{  commutes' := λ r, rfl,
   ..algebra_map R S }

def tensor_algebra.quot :
  free_algebra R M →ₐ[R] tensor_algebra R M :=
ring_quot.mk_alg_hom R (tensor_algebra.rel R M)


def power (n : ℕ) : submodule R (tensor_algebra R M) :=
submodule.span R (set.range $ @tensor_algebra.mk R _ M _ _ n)

variables [comm_semiring R] [add_comm_monoid M] [semimodule R M]


open exterior_algebra homological_complex tensor_algebra


def of_scalar : R →ₐ[R] exterior_algebra R M :=
(exterior_algebra.quot R M).comp
((ring_quot.mk_alg_hom R (tensor_algebra.rel R M)).comp
(algebra_alg_hom R (free_algebra R M)))


def lift {B : Type*} [add_comm_monoid B] [semimodule R B] (n : ℕ)
  (f : @multilinear_map R (fin n) (λ i, M) B _ _ _ _ _ _) :
   power R M n →ₗ[R] B :=
{ to_fun := λ x, quot.lift_on x,
  map_add' := _,
  map_smul' := _ }

--def power (n : ℕ) : submodule R (tensor_algebra R M) :=

def hm : submodule.span R (set.range (@wedge R _ M _ _ 0)) ≃ₗ[R] R :=
{ to_fun := _,
  map_add' := _,
  map_smul' := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _ }

class is_power (n : ℕ) (N : Module R) :=
(quot : @multilinear_map R (fin n) (λ i, M) N _ _ _ _ _ _)
(property : ∀ (B : Module R) (f : @multilinear_map R (fin n) (λ i, M) B _ _ _ _ _ _),
 ∃! F : N →ₗ[R] B, F.comp_multilinear_map quot = f)
#print prefix power
def power_to_algebra (n : ℕ) (N : Module R) [is_power R M n N] :
  N →ₗ[R] tensor_algebra R M :=
{ to_fun := λ x, is_power.property
  map_add' := _,
  map_smul' := _ }


#exit
--if h : n = 0 then subalgebra.to_submodule (of_scalar R M).range else
--submodule.span R (set.range (@wedge R _ M _ _ n))
variables {R M}
lemma power_zero (n : ℕ) (h : n = 0) :
  power R M n = subalgebra.to_submodule (of_scalar R M).range :=
if_pos h

lemma power_nonzero (n : ℕ) (h : n ≠ 0) :
  power R M n = submodule.span R (set.range (@wedge R _ M _ _ n)) :=
if_neg h
variables (R)
-- m ∈ M corresponds to φ ∈ Hom(R, M)
def power_diff (i : ℕ) (x : M) : power R M i.succ →ₗ[R] power R M i :=
linear_map.cod_restrict _ ((algebra.lmul R _ $ ι R x).comp (submodule.subtype _)) $
  begin
    suffices : ∀ y ∈ set.range (@wedge R _ M _ _ i.succ),
      algebra.lmul R (exterior_algebra R M) (ι R x) y ∈ set.range (@wedge R _ M _ _ i), by
    {intro c,
    unfold power,
    split_ifs,

    rw power_nonzero _ (nat.succ_ne_zero _),},
    rintro ⟨y, hy⟩,
    rw power_nonzero _ (nat.succ_ne_zero _) at hy,
    /-suffices : ((algebra.lmul R (exterior_algebra R M) $ ι R x).comp (submodule.subtype $ power R M i.succ)).range ≤ power R M i,
    from λ c, this (linear_map.mem_range.2 ⟨c, rfl⟩),
    --erw submodule.map_span,
    rw power_nonzero _ (nat.succ_ne_zero _),
    unfold linear_map.range,
    erw submodule.map_span,-/


  end

variables [comm_ring R] [add_comm_group M] [module R M]

structure koszul_complex (x : M) :=
(C : chain_complex (Module R))
(iso_at_nat : ∀ n : ℕ, C.X n ≅ Module.of R (power R M n))
(bdd_below : bounded_below_by C 0)
(differential : ∀ i, C.d i = sorry)

end exterior_algebra
-/
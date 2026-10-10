import YesMetaZFC.SetTheory.InnerModel.Order.LocalSuccessor

/-! # 有序状态的总坐标读取

正常输入读取 Kuratowski 对的坐标；非对输入返回空集。因此递归算子在所有集合
输入上都有定义，而真实递归历史的值仍由原配对图验证。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rp_coord_d (i : Bool) (p x y : M.Domain) : Prop := if i then KPair_d M p y x else KPair_d M p x y
def rp_coord_m {n} (i : Bool) (p x y : Term n) : Formula 1 n := if i then kpair0_m p y x else kpair0_m p x y
@[simp] theorem rp_coord_closed_l {n} (i : Bool) (p x y : Term n)
    (hp : p.freeSupport = []) (hx : x.freeSupport = []) (hy : y.freeSupport = []) : (rp_coord_m i p x y).FreeClosed := by
  cases i <;> simp -implicitDefEqProofs [rp_coord_m, hp, hx, hy]
theorem rp_coord_delta_l {n} (i : Bool) (p x y : Term n) : (rp_coord_m i p x y).IsDelta0 := by
  cases i <;> exact kpair0_delta_l ..
theorem rp_coord_sat_l (hE : Extensional M) {n} (ρ : Env M n) (i : Bool) (p x y : Term n) :
    Formula.satisfies ρ (rp_coord_m i p x y) ↔ Rp_coord_d i (p.eval ρ) (x.eval ρ) (y.eval ρ) := by
  cases i <;> exact kpair0_sat_l hE ..

def Rp_proj_d (i : Bool) (p x : M.Domain) : Prop :=
  (∃ y, Rp_coord_d i p x y) ∨ (¬ Ri_valid_d p ∧ ∀ z, ¬ M.mem z x)
def rp_proj_m {n} (i : Bool) (p x : Term n) : Formula 1 n :=
  .disj (Formula.existsMem p (Formula.existsMem .newest (rp_coord_m i p.weaken.weaken x.weaken.weaken .newest)))
    (.conj (.neg (ri_valid_m p)) (Formula.forallMem x .falsum))
derive_free_closed rp_proj_m
theorem rp_proj_delta_l {n} (i : Bool) (p x : Term n) : (rp_proj_m i p x).IsDelta0 :=
  .disj (.existsMem _ (.existsMem _ (rp_coord_delta_l ..))) (.conj (.neg (ri_valid_delta_l _)) (.forallMem _ .falsum))
theorem rp_proj_sat_l (hE : Extensional M) {n} (ρ : Env M n) (i : Bool) (p x : Term n) :
    Formula.satisfies ρ (rp_proj_m i p x) ↔ Rp_proj_d i (p.eval ρ) (x.eval ρ) := by
  simp only [rp_proj_m, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff,
    rp_coord_sat_l hE, ri_valid_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  apply or_congr _ Iff.rfl
  constructor
  · rintro ⟨_, _, y, _, h⟩; exact ⟨y, h⟩
  · rintro ⟨y, h⟩
    have hy : ∃ s, M.mem s (p.eval ρ) ∧ M.mem y s := by
      cases i
      · exact (kpair_union_l M h y).mpr (Or.inr rfl)
      · exact (kpair_union_l M h y).mpr (Or.inl rfl)
    obtain ⟨s, hs, hy⟩ := hy
    exact ⟨s, hs, y, hy, h⟩

def rp_proj_s (i : Bool) : Delta0BinarySchema 0 where
  body := rp_proj_m i (.bound 1) .newest
  freeClosed := by simp -implicitDefEqProofs
  delta0 := rp_proj_delta_l ..
theorem rp_proj_schema_l (hE : Extensional M) (ρ : Env M 0) (i : Bool) (p x : M.Domain) :
    (rp_proj_s i).toBinarySchema.denote ρ p x ↔ Rp_proj_d i p x := rp_proj_sat_l hE _ _ _ _

theorem rp_proj_total_l (hKP : M.Models KP) (i : Bool) (p : M.Domain) : ∃ x, Rp_proj_d i p x := by
  classical
  by_cases hp : Ri_valid_d p
  · obtain ⟨a, b, hp⟩ := hp
    cases i
    · exact ⟨a, Or.inl ⟨b, hp⟩⟩
    · exact ⟨b, Or.inl ⟨a, hp⟩⟩
  · obtain ⟨E, he⟩ := KP.exists_empty hKP; exact ⟨E, Or.inr ⟨hp, he⟩⟩

theorem rp_proj_unique_l (hE : Extensional M) {i p x y} (h : Rp_proj_d (M := M) i p x) (g : Rp_proj_d i p y) : x = y := by
  have valid {x y} (h : Rp_coord_d i p x y) : Ri_valid_d p := by
    cases i
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩
  rcases h with ⟨a, h⟩ | ⟨hp, hx⟩ <;> rcases g with ⟨b, g⟩ | ⟨hp', hy⟩
  · cases i
    · exact (kpair_injective_l M h g).1
    · exact (kpair_injective_l M h g).2
  · exact (hp' (valid h)).elim
  · exact (hp (valid g)).elim
  · exact hE.eq_of_same_members x y (fun z => iff_of_false (hx z) (hy z))

theorem rp_proj_pair_l (hE : Extensional M) {p U R x : M.Domain} (hp : KPair_d M p U R) (i : Bool) :
    Rp_proj_d i p x ↔ x = if i then R else U := by
  have hx : Rp_proj_d i p (if i then R else U) := by cases i <;> exact Or.inl ⟨_, hp⟩
  exact ⟨fun h => rp_proj_unique_l hE h hx, fun h => h ▸ hx⟩

end YesMetaZFC.SetTheory.InnerModel

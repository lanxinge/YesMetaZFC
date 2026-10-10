import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra

/-! # 两个传递源的共同秩层

若源秩层已被目标覆盖，且目标中该层各对象的子集都能回到源，逐层幂集
递归便相同。比较原历史即可，不要求任一完整历史属于另一源。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem vr_cross_l (hZF : M.Models ZF) {X Y L U V : M.Domain}
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hU : M.mem U X) (hV : M.mem V Y)
    (rx : Vr_d X L U) (ry : Vr_d Y L V) (inside : M.MemberSubset U Y)
    (subsets : ∀ A, M.mem A U → ∀ t, M.mem t Y → M.MemberSubset t A → M.mem t X) : U = V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ut := rx.transitive_l hZF hX hU
  obtain ⟨B, F, hB, _, hx⟩ := rx
  obtain ⟨C, G, hC, _, hy⟩ := ry
  have ff := (hx U hU).2.1
  have gf := (hy V hV).2.1
  have ho := (hx U hU).1
  have member δ A (ha : Rd_entry_d δ A F) : M.mem A U :=
    ((hx A (hX B hB A (ff.bound_l ha).2)).2.2.2).mpr
      ⟨δ, (ff.bound_l ha).1, A, (ff.bound_l ha).2, ha, fun _ h => h⟩
  have compare δ A D (ha : M.mem A X) (hd : M.mem D Y) (low : M.MemberSubset A U) (bound : M.MemberSubset δ L)
      (left : ∀ t, M.mem t X → Vc_step_d δ B F A t)
      (right : ∀ t, M.mem t Y → Vc_step_d δ C G D t)
      (prev : ∀ γ, M.mem γ δ → ∀ P Q, Rd_entry_d γ P F → Rd_entry_d γ Q G → P = Q) : A = D := by
    apply hZF.1.eq_of_same_members A D
    intro x
    constructor
    · intro hxa
      obtain ⟨γ, hγ, P, _, hp, sub⟩ := (left x (hX A ha x hxa)).mp hxa
      obtain ⟨Q, hQ, hq⟩ := gf.2.1 γ (bound γ hγ)
      exact (right x (inside x (low x hxa))).mpr ⟨γ, hγ, Q, hQ, hq, prev γ hγ P Q hp hq ▸ sub⟩
    · intro hxd
      have hxy := hY D hd x hxd
      obtain ⟨γ, hγ, Q, _, hq, sub⟩ := (right x hxy).mp hxd
      obtain ⟨P, hP, hp⟩ := ff.2.1 γ (bound γ hγ)
      have sub' : M.MemberSubset x P := (prev γ hγ P Q hp hq).symm ▸ sub
      exact (left x (subsets P (member γ P hp) x hxy sub')).mpr ⟨γ, hγ, P, hP, hp, sub'⟩
  let ρ : Env M 3 := ⟨Fin.cases L (Fin.cases F (fun _ => G)), fun _ => L⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (.forallE (.forallE
    (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 4)) (.imp
      (rd_entry0_m (.bound 2) .newest (.bound 5)) (Formula.extensionalEq (.bound 1) .newest))))) }
  have sat δ : φ.denote ρ δ ↔ M.mem δ L → ∀ A D, Rd_entry_d δ A F → Rd_entry_d δ D G → A = D := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all δ (hδ : M.mem δ L) : ∀ A D, Rd_entry_d δ A F → Rd_entry_d δ D G → A = D := by
    apply (sat δ).mp (ZF.mem_ind_l M hZF I φ ρ ?_ δ) hδ
    intro δ ih
    apply (sat δ).mpr
    intro hδ A D ha hd
    exact compare δ A D (hX B hB A (ff.bound_l ha).2) (hY C hC D (gf.bound_l hd).2)
      (ut A (member δ A ha)) (ho.transitive δ hδ)
      (fun t ht => (hx t ht).2.2.1 δ hδ A (ff.bound_l ha).2 ha)
      (fun t ht => (hy t ht).2.2.1 δ hδ D (gf.bound_l hd).2 hd)
      (fun γ hγ => (sat γ).mp (ih γ hγ) (ho.transitive δ hδ γ hγ))
  exact compare L U V hU hV (fun _ h => h) (fun _ h => h)
    (fun t ht => (hx t ht).2.2.2) (fun t ht => (hy t ht).2.2.2) all

end YesMetaZFC.SetTheory

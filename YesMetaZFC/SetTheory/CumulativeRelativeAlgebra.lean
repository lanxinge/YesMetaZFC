import YesMetaZFC.SetTheory.CumulativeRelative

/-! # 相对秩层的传递性与唯一性

对给定历史作模型内成员归纳。只比较载体已经包含的对象，既不将相对幂集
偷换为背景幂集，也不要求载体满足完整 ZF。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem Vr_d.transitive_l {Z α V : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (h : Vr_d Z α V) : M.TransitiveSet V := by
  obtain ⟨B, F, hB, _, cert⟩ := h
  have ho := (cert V hV).1
  have hf := (cert V hV).2.1
  have step β W (hW : M.mem W Z) (eqn : ∀ t, M.mem t Z → Vc_step_d β B F W t)
      (ih : ∀ γ, M.mem γ β → ∀ U, Rd_entry_d γ U F → M.TransitiveSet U) : M.TransitiveSet W := by
    intro x hx y hy
    obtain ⟨γ, hγ, U, hU, hγU, sub⟩ := (eqn x (hZ W hW x hx)).mp hx
    exact (eqn y (hZ x (hZ W hW x hx) y hy)).mpr
      ⟨γ, hγ, U, hU, hγU, (ih γ hγ U hγU) y (sub y hy)⟩
  let ρ : Env M 2 := ⟨Fin.cases α (fun _ => F), fun _ => α⟩
  let φ : UnarySchema 2 := { body := .imp (.mem .newest (.bound 1)) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 3)) (Formula.isTransitive .newest))) }
  have sat β : φ.denote ρ β ↔ M.mem β α → ∀ W, Rd_entry_d β W F → M.TransitiveSet W := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_isTransitive_iff]; rfl
  have all β (hβ : M.mem β α) : ∀ W, Rd_entry_d β W F → M.TransitiveSet W := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ W hβW
    exact step β W (hZ B hB W (hf.bound_l hβW).2)
      (fun t ht => (cert t ht).2.2.1 β hβ W (hf.bound_l hβW).2 hβW)
      (fun γ hγ => (sat γ).mp (ih γ hγ) (ho.transitive β hβ γ hγ))
  exact step α V hV (fun t ht => (cert t ht).2.2.2) all

theorem Vr_d.unique_l {Z α V W : M.Domain} (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hW : M.mem W Z) (h : Vr_d Z α V) (k : Vr_d Z α W) : V = W := by
  obtain ⟨B, F, hB, _, hc⟩ := h
  obtain ⟨C, G, hC, _, kc⟩ := k
  have hf := (hc V hV).2.1
  have hg := (kc W hW).2.1
  have ho := (hc V hV).1
  have compare β U U' (hU : M.mem U Z) (hU' : M.mem U' Z) (sub : M.MemberSubset β α)
      (hu : ∀ t, M.mem t Z → Vc_step_d β B F U t)
      (hv : ∀ t, M.mem t Z → Vc_step_d β C G U' t)
      (prev : ∀ γ, M.mem γ β → ∀ A A', Rd_entry_d γ A F → Rd_entry_d γ A' G → A = A') : U = U' := by
    apply hZF.1.eq_of_same_members U U'
    intro x
    constructor
    · intro hx
      obtain ⟨γ, hγ, A, _, hγA, hxA⟩ := (hu x (hZ U hU x hx)).mp hx
      obtain ⟨A', hA', hγA'⟩ := hg.2.1 γ (sub γ hγ)
      exact (hv x (hZ U hU x hx)).mpr ⟨γ, hγ, A', hA', hγA', prev γ hγ A A' hγA hγA' ▸ hxA⟩
    · intro hx
      obtain ⟨γ, hγ, A', _, hγA', hxA'⟩ := (hv x (hZ U' hU' x hx)).mp hx
      obtain ⟨A, hA, hγA⟩ := hf.2.1 γ (sub γ hγ)
      exact (hu x (hZ U' hU' x hx)).mpr ⟨γ, hγ, A, hA, hγA, (prev γ hγ A A' hγA hγA').symm ▸ hxA'⟩
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases F (fun _ => G)), fun _ => α⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (.forallE (.forallE
    (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 4)) (.imp
      (rd_entry0_m (.bound 2) .newest (.bound 5)) (Formula.extensionalEq (.bound 1) .newest))))) }
  have sat β : φ.denote ρ β ↔ M.mem β α → ∀ U U', Rd_entry_d β U F → Rd_entry_d β U' G → U = U' := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all β (hβ : M.mem β α) : ∀ U U', Rd_entry_d β U F → Rd_entry_d β U' G → U = U' := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ U U' hu hv
    exact compare β U U' (hZ B hB U (hf.bound_l hu).2) (hZ C hC U' (hg.bound_l hv).2)
      (ho.transitive β hβ) (fun t ht => (hc t ht).2.2.1 β hβ U (hf.bound_l hu).2 hu)
      (fun t ht => (kc t ht).2.2.1 β hβ U' (hg.bound_l hv).2 hv)
      (fun γ hγ => (sat γ).mp (ih γ hγ) (ho.transitive β hβ γ hγ))
  exact compare α V W hV hW (fun _ h => h) (fun t ht => (hc t ht).2.2.2)
    (fun t ht => (kc t ht).2.2.2) all

end YesMetaZFC.SetTheory

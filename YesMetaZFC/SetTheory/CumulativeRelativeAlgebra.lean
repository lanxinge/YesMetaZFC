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

theorem vc_transitive_l {Z α V B F : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (hB : M.mem B Z) (cert : ∀ t, M.mem t Z → Vc_d α V B F t) :
    M.TransitiveSet V ∧ ∀ β, M.mem β α → ∀ W, Rd_entry_d β W F → M.TransitiveSet W := by
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
  exact ⟨step α V hV (fun t ht => (cert t ht).2.2.2) all, all⟩

theorem Vr_d.transitive_l {Z α V : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (h : Vr_d Z α V) : M.TransitiveSet V := by
  obtain ⟨_, _, hB, _, cert⟩ := h
  exact (vc_transitive_l hZF hZ hV hB cert).1

/-- 相对 Vα 仍包含 α 的全部序数；这里只用给定历史，不要求载体满足 ZF。 -/
theorem Vr_d.ordinal_subset_l {Z α V : M.Domain} (hZ : M.TransitiveSet Z) (hV : M.mem V Z)
    (h : Vr_d Z α V) : M.MemberSubset α V := by
  obtain ⟨B, F, _, hF, cert⟩ := h
  have ho := (cert V hV).1
  have hf := (cert V hV).2.1
  have domain β (hβ : M.mem β α) : M.mem β Z := by
    obtain ⟨W, _, p, hp, hpf⟩ := hf.2.1 β hβ
    exact (hp.mem_l M hZ (hZ F hF p hpf)).1
  let ρ : Env M 2 := ⟨Fin.cases α (fun _ => F), fun _ => α⟩
  let φ : UnarySchema 2 := { body := .imp (.mem .newest (.bound 1)) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 3)) (Formula.subset (.bound 1) .newest))) }
  have sat β : φ.denote ρ β ↔ M.mem β α → ∀ W, Rd_entry_d β W F → M.MemberSubset β W := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff]; rfl
  have all β (hβ : M.mem β α) : ∀ W, Rd_entry_d β W F → M.MemberSubset β W := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ W hβW γ hγ
    have hγα := ho.transitive β hβ γ hγ
    obtain ⟨U, hU, hγU⟩ := hf.2.1 γ hγα
    exact ((cert γ (domain γ hγα)).2.2.1 β hβ W (hf.bound_l hβW).2 hβW).mpr
      ⟨γ, hγ, U, hU, hγU, (sat γ).mp (ih γ hγ) hγα U hγU⟩
  intro β hβ
  obtain ⟨W, hW, hβW⟩ := hf.2.1 β hβ
  exact ((cert β (domain β hβ)).2.2.2).mpr ⟨β, hβ, W, hW, hβW, all β hβ W hβW⟩

theorem Vr_d.compare_l {Z α β V W : M.Domain} (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hW : M.mem W Z) (h : Vr_d Z α V) (k : Vr_d Z β W)
    (sub : M.MemberSubset β α) : M.MemberSubset W V ∧ (M.mem β α → M.mem W V) := by
  obtain ⟨B, F, hB, _, hc⟩ := h
  obtain ⟨C, G, hC, _, kc⟩ := k
  have hf := (hc V hV).2.1
  have hg := (kc W hW).2.1
  have ho := (kc W hW).1
  have compare δ U U' (hU : M.mem U Z) (hU' : M.mem U' Z) (sm : M.MemberSubset δ β)
      (hu : ∀ t, M.mem t Z → Vc_step_d δ B F U t)
      (hv : ∀ t, M.mem t Z → Vc_step_d δ C G U' t)
      (prev : ∀ γ, M.mem γ δ → ∀ A A', Rd_entry_d γ A F → Rd_entry_d γ A' G → A = A') : U = U' := by
    apply hZF.1.eq_of_same_members U U'
    intro x
    constructor
    · intro hx
      obtain ⟨γ, hγ, A, _, hγA, hxA⟩ := (hu x (hZ U hU x hx)).mp hx
      obtain ⟨A', hA', hγA'⟩ := hg.2.1 γ (sm γ hγ)
      exact (hv x (hZ U hU x hx)).mpr ⟨γ, hγ, A', hA', hγA', prev γ hγ A A' hγA hγA' ▸ hxA⟩
    · intro hx
      obtain ⟨γ, hγ, A', _, hγA', hxA'⟩ := (hv x (hZ U' hU' x hx)).mp hx
      obtain ⟨A, hA, hγA⟩ := hf.2.1 γ (sub γ (sm γ hγ))
      exact (hu x (hZ U' hU' x hx)).mpr ⟨γ, hγ, A, hA, hγA, (prev γ hγ A A' hγA hγA').symm ▸ hxA'⟩
  let ρ : Env M 3 := ⟨Fin.cases β (Fin.cases F (fun _ => G)), fun _ => β⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (.forallE (.forallE
    (.imp (rd_entry0_m (.bound 2) (.bound 1) (.bound 4)) (.imp
      (rd_entry0_m (.bound 2) .newest (.bound 5)) (Formula.extensionalEq (.bound 1) .newest))))) }
  have sat δ : φ.denote ρ δ ↔ M.mem δ β → ∀ U U', Rd_entry_d δ U F → Rd_entry_d δ U' G → U = U' := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all δ (hδ : M.mem δ β) : ∀ U U', Rd_entry_d δ U F → Rd_entry_d δ U' G → U = U' := by
    apply (sat δ).mp (ZF.mem_ind_l M hZF I φ ρ ?_ δ) hδ
    intro δ ih
    apply (sat δ).mpr
    intro hδ U U' hu hv
    exact compare δ U U' (hZ B hB U (hf.bound_l hu).2) (hZ C hC U' (hg.bound_l hv).2)
      (ho.transitive δ hδ) (fun t ht => (hc t ht).2.2.1 δ (sub δ hδ) U (hf.bound_l hu).2 hu)
      (fun t ht => (kc t ht).2.2.1 δ hδ U' (hg.bound_l hv).2 hv)
      (fun γ hγ => (sat γ).mp (ih γ hγ) (ho.transitive δ hδ γ hγ))
  have member x (hx : M.mem x W) : M.mem x V := by
    have hxZ := hZ W hW x hx
    obtain ⟨δ, hδ, Q, _, hδQ, hxQ⟩ := ((kc x hxZ).2.2.2).mp hx
    obtain ⟨P, hP, hδP⟩ := hf.2.1 δ (sub δ hδ)
    exact ((hc x hxZ).2.2.2).mpr ⟨δ, sub δ hδ, P, hP, hδP, (all δ hδ P Q hδP hδQ).symm ▸ hxQ⟩
  refine ⟨member, fun hβ => ?_⟩
  obtain ⟨P, hP, hβP⟩ := hf.2.1 β hβ
  have eq := compare β P W (hZ B hB P hP) hW (fun _ h => h)
    (fun x hx => (hc x hx).2.2.1 β hβ P hP hβP) (fun x hx => (kc x hx).2.2.2) all
  exact ((hc W hW).2.2.2).mpr ⟨β, hβ, P, hP, hβP, fun x hx => eq.symm ▸ hx⟩

theorem Vr_d.unique_l {Z α V W : M.Domain} (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hW : M.mem W Z) (h : Vr_d Z α V) (k : Vr_d Z α W) : V = W :=
  hZF.1.eq_of_same_members V W (fun x => ⟨(k.compare_l hZF hZ hW hV h (fun _ h => h)).1 x,
    (h.compare_l hZF hZ hV hW k (fun _ h => h)).1 x⟩)

/-- 极限相对秩层包含源中已有的配对；只提高有限个层号。 -/
theorem Vr_d.pair_mem_l {Z α V x y p : M.Domain} (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α)
    (hx : M.mem x V) (hy : M.mem y V) (hpZ : M.mem p Z) (hp : Pair_d M p x y) : M.mem p V := by
  obtain ⟨B, F, _, _, cert⟩ := hv
  have fn := (cert V hV).2.1
  have hxZ := hZ V hV x hx
  have hyZ := hZ V hV y hy
  obtain ⟨β, hβ, P, hP, hβP, hxP⟩ := ((cert x hxZ).2.2.2).mp hx
  obtain ⟨γ, hγ, Q, hQ, hγQ, hyQ⟩ := ((cert y hyZ).2.2.2).mp hy
  have joint : ∃ δ, M.mem δ α ∧ M.mem β δ ∧ M.mem γ δ := by
    rcases hα.1.wellOrder.linear.compare β hβ γ hγ with eq | lt | gt
    · obtain ⟨δ, hδ, hγδ⟩ := hα.2.2 γ hγ
      exact ⟨δ, hδ, hZF.1.eq_of_same_members β γ eq ▸ hγδ, hγδ⟩
    · obtain ⟨δ, hδ, hγδ⟩ := hα.2.2 γ hγ
      exact ⟨δ, hδ, (hα.1.mem hδ).transitive γ hγδ β lt, hγδ⟩
    · obtain ⟨δ, hδ, hβδ⟩ := hα.2.2 β hβ
      exact ⟨δ, hδ, hβδ, (hα.1.mem hδ).transitive β hβδ γ gt⟩
  obtain ⟨δ, hδ, hβδ, hγδ⟩ := joint
  obtain ⟨U, hU, hδU⟩ := fn.2.1 δ hδ
  have hxU := ((cert x hxZ).2.2.1 δ hδ U hU hδU).mpr ⟨β, hβδ, P, hP, hβP, hxP⟩
  have hyU := ((cert y hyZ).2.2.1 δ hδ U hU hδU).mpr ⟨γ, hγδ, Q, hQ, hγQ, hyQ⟩
  exact ((cert p hpZ).2.2.2).mpr ⟨δ, hδ, U, hU, hδU,
    fun t ht => ((hp t).mp ht).elim (fun eq => eq ▸ hxU) (fun eq => eq ▸ hyU)⟩

theorem Vr_d.kpair_mem_l {Z α V x y p : M.Domain} (hZ : M.TransitiveSet Z)
    (hV : M.mem V Z) (hv : Vr_d Z α V) (hα : M.IsLimitOrdinal α)
    (hx : M.mem x V) (hy : M.mem y V) (hpZ : M.mem p Z) (hp : KPair_d M p x y) : M.mem p V := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  have hsZ := hZ p hpZ s ((hp s).mpr (Or.inl rfl))
  have htZ := hZ p hpZ t ((hp t).mpr (Or.inr rfl))
  have hsV := hv.pair_mem_l hZF hZ hV hα hx hx hsZ
    (fun z => (hs z).trans ⟨Or.inl, fun h => h.elim id id⟩)
  exact hv.pair_mem_l hZF hZ hV hα hsV (hv.pair_mem_l hZF hZ hV hα hx hy htZ ht) hpZ hp

end YesMetaZFC.SetTheory

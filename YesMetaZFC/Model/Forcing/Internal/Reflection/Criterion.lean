import YesMetaZFC.Model.Forcing.Internal.Reflection.Countermodel

/-! # 带原模型定义条件的全局力迫判据

把原模型条件、名称参数和失败的力迫同时反射到实际可数模型。在该模型中
构造通过反例条件的泛型；因而可直接消费已证明的、对所有泛型成立的名称构造。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

/-- 在实际可数地模型中，遍历通过原条件的泛型即可判定力迫；只使用原 ZF。 -/
theorem forces_countable_l {M : SetTheory.Structure.{u}} {B R z : M.Domain}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) (e : Nat → M.Domain) (he : Function.Surjective e)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (ρ : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i)) {p} (hp : M.mem p B) (hz : p ≠ z)
    (valid : ∀ U, Generic_d M B R z U → U p →
      ∀ η : Env (extension_l M hZF B R z U) n,
        (∀ i, Qval_d M B R z U (ρ.bound i) (η.bound i)) → Formula.satisfies η φ) :
    Forces_d M B R z φ ρ p := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨a, ha⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have haN := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B a ha
  let σ : Env M n := ⟨ρ.bound, fun _ => a⟩
  have hσ : ∀ t : Term n, Name_d M B (t.eval σ) := by
    intro t
    cases t with
    | free _ => exact haN
    | bound i => exact hρ i
  have hnσ : ¬ Forces_d M B R z φ σ p :=
    fun h => hn ((forces_env_l hZF.1 φ hφ ρ σ (fun _ => rfl) p).mpr h)
  obtain ⟨r, hr, hneg⟩ := regular_neg_witness_l (forces_regular_l O hZF φ σ hσ) hp hz hnσ
  obtain ⟨U, hU, hrU⟩ := internal_generic_l O e he hr.1 hr.2.1
  let η := qenv_l (R := R) (z := z) (U := U) hZF σ hσ
  have hv := qenv_val_l (R := R) (z := z) (U := U) hZF σ hσ
  have hnot := (Formula.satisfies_neg_iff η φ).mp
    ((forcing_truth_l O hZF hU (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ)
      σ η hv).mp ⟨r, hrU, (forces_neg_l hZF.1 φ σ r).mpr hneg⟩)
  exact hnot (valid U hU (hU.upward r p hrU hp hr.2.2) η (fun i => hv (.bound i)))

/-- 同时反射原模型的指定理论及有限参数，泛型论证因而保留实际使用的公理强度。 -/
theorem source_of_generics_theory_l {Γ : SetTheory.Theory} {n} (α β : Formula 1 n) (hα : α.FreeClosed) (hβ : β.FreeClosed)
    (B R z p : Term n) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = [])
    (valid : ∀ N : SetTheory.Structure.{u}, N.Models ZF → N.Models Γ → ∀ η : Env N n,
      Cond_order_d N (B.eval η) (R.eval η) (z.eval η) → Formula.satisfies η α →
      ∀ U, Generic_d N (B.eval η) (R.eval η) (z.eval η) U → U (p.eval η) → Formula.satisfies η β)
    {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) (hΓ : M.Models Γ) (ρ : Env M n)
    (O : Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ))
    (hpos : M.mem (p.eval ρ) (B.eval ρ)) (hne : p.eval ρ ≠ z.eval ρ) (hraw : Formula.satisfies ρ α) :
    Formula.satisfies ρ β := by
  obtain ⟨N, hE, hTheory, η, tr, e, he⟩ := FirstOrderSemantics.countable_env_l M hZF.1 ρ
  have hN := (hTheory ZF).mpr hZF
  have L : Cond_order_d N (B.eval η) (R.eval η) (z.eval η) :=
    (cond_order_sat_l hE η B R z).mp ((tr _ (cond_order_m_freeClosed _ _ _ hB hR hz)).mp
      ((cond_order_sat_l hZF.1 ρ B R z).mpr O))
  have hpos' : N.mem (p.eval η) (B.eval η) :=
    (Formula.satisfies_mem_iff η p B).mp ((tr (.mem p B)
      (by simp only [Definitional.Formula.FreeClosed]; exact ⟨hp, hB⟩)).mp
        ((Formula.satisfies_mem_iff ρ p B).mpr hpos))
  have heq : p.eval ρ = z.eval ρ ↔ p.eval η = z.eval η := by
    have hh := tr (Formula.extensionalEq p z) ((Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨hp, hz⟩)
    simpa only [Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_extensionalEq_iff_eq hE] using hh
  obtain ⟨U, hU, hpU⟩ := internal_generic_l L e he hpos' (fun hh => hne (heq.mpr hh))
  exact (tr β hβ).mpr (valid N hN ((hTheory Γ).mpr hΓ) η L ((tr α hα).mp hraw) U hU hpU)

/-- 若每个被接受的正条件泛型都给出原模型中的见证，有限参数反射消去泛型存在前提。 -/
theorem source_of_generics_l {n} (α β : Formula 1 n) (hα : α.FreeClosed) (hβ : β.FreeClosed)
    (B R z p : Term n) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = [])
    (valid : ∀ N : SetTheory.Structure.{u}, N.Models ZF → ∀ η : Env N n,
      Cond_order_d N (B.eval η) (R.eval η) (z.eval η) → Formula.satisfies η α →
      ∀ U, Generic_d N (B.eval η) (R.eval η) (z.eval η) U → U (p.eval η) → Formula.satisfies η β)
    {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) (ρ : Env M n)
    (O : Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ))
    (hpos : M.mem (p.eval ρ) (B.eval ρ)) (hne : p.eval ρ ≠ z.eval ρ) (hraw : Formula.satisfies ρ α) :
    Formula.satisfies ρ β :=
  source_of_generics_theory_l (Γ := ZF) α β hα hβ B R z p hB hR hz hp
    (fun N hN _ => valid N hN) hZF hZF ρ O hpos hne hraw

/-- 原模型条件由实际公式 α 给出，名称参数由闭项代入指定；不要求原模型可数。 -/
theorem forces_of_generics_l {n k} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (α : Formula 1 k) (hα : α.FreeClosed) (e : Fin n → Term k) (B R z p : Term k)
    (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hp : p.freeSupport = [])
    (valid : ∀ N : SetTheory.Structure.{u}, ∀ hN : N.Models ZF, ∀ η : Env N k,
      Cond_order_d N (B.eval η) (R.eval η) (z.eval η) →
      (∀ i, Name_d N (B.eval η) ((e i).eval η)) → N.mem (p.eval η) (B.eval η) → p.eval η ≠ z.eval η →
      Formula.satisfies η α → ∀ U, Generic_d N (B.eval η) (R.eval η) (z.eval η) U → U (p.eval η) →
      ∀ ξ : Env (extension_l N hN (B.eval η) (R.eval η) (z.eval η) U) n,
        (∀ i, Qval_d N (B.eval η) (R.eval η) (z.eval η) U ((e i).eval η) (ξ.bound i)) → Formula.satisfies ξ φ)
    {M : SetTheory.Structure.{u}} (hZF : M.Models ZF) (ρ : Env M k)
    (O : Cond_order_d M (B.eval ρ) (R.eval ρ) (z.eval ρ))
    (hn : ∀ i, Name_d M (B.eval ρ) ((e i).eval ρ))
    (hpos : M.mem (p.eval ρ) (B.eval ρ)) (hne : p.eval ρ ≠ z.eval ρ) (hraw : Formula.satisfies ρ α) :
    Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (p.eval ρ) := by
  apply Classical.byContradiction
  intro hfail
  obtain ⟨N, hE, hTheory, η, tr, f, hf⟩ := FirstOrderSemantics.countable_env_l M hZF.1 ρ
  have hN := (hTheory ZF).mpr hZF
  have L : Cond_order_d N (B.eval η) (R.eval η) (z.eval η) :=
    (cond_order_sat_l hE η B R z).mp ((tr _ (cond_order_m_freeClosed _ _ _ hB hR hz)).mp
      ((cond_order_sat_l hZF.1 ρ B R z).mpr O))
  have names i : Name_d N (B.eval η) ((e i).eval η) :=
    (name_sat_l N hE η B (e i)).mp ((tr _ (name_m_freeClosed _ _ hB (he i))).mp
      ((name_sat_l M hZF.1 ρ B (e i)).mpr (hn i)))
  have hpos' : N.mem (p.eval η) (B.eval η) :=
    (Formula.satisfies_mem_iff η p B).mp ((tr (.mem p B)
      (by simp only [Definitional.Formula.FreeClosed]; exact ⟨hp, hB⟩)).mp
        ((Formula.satisfies_mem_iff ρ p B).mpr hpos))
  have heq : p.eval ρ = z.eval ρ ↔ p.eval η = z.eval η := by
    have h := tr (Formula.extensionalEq p z) ((Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨hp, hz⟩)
    simpa only [Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_extensionalEq_iff_eq hE] using h
  have hne' : p.eval η ≠ z.eval η := fun hh => hne (heq.mpr hh)
  let σ : Env N n := ⟨fun i => (e i).eval η, η.free⟩
  have hnσ : ¬ Forces_d N (B.eval η) (R.eval η) (z.eval η) φ σ (p.eval η) := by
    intro hh
    exact hfail ((force_at_sat_l φ ρ e B R z p).mp
      ((tr (force_at_m φ e B R z p) (force_at_closed_l _ _ _ _ _ _ hφ he hB hR hz hp)).mpr
        ((force_at_sat_l φ η e B R z p).mpr hh)))
  obtain ⟨a, ha⟩ := KP.exists_empty (ZF.modelsKP hN)
  have haN := name_empty_l N (KP.exists_pair (ZF.modelsKP hN)) (B.eval η) a ha
  let δ : Env N n := ⟨σ.bound, fun _ => a⟩
  have hδ : ∀ t : Term n, Name_d N (B.eval η) (t.eval δ) := by
    intro t
    cases t with
    | free _ => exact haN
    | bound i => exact names i
  have hnδ : ¬ Forces_d N (B.eval η) (R.eval η) (z.eval η) φ δ (p.eval η) :=
    fun hh => hnσ ((forces_env_l hE φ hφ σ δ (fun _ => rfl) _).mpr hh)
  obtain ⟨r, hr, hneg⟩ := regular_neg_witness_l (forces_regular_l L hN φ δ hδ) hpos' hne' hnδ
  obtain ⟨U, hU, hrU⟩ := internal_generic_l L f hf hr.1 hr.2.1
  have hpU := hU.upward r (p.eval η) hrU hpos' hr.2.2
  let E := extension_l N hN (B.eval η) (R.eval η) (z.eval η) U
  let ξ : Env E n := qenv_l hN δ hδ
  have hv : Env_val_d hN δ ξ := qenv_val_l hN δ hδ
  have hnot : ¬ Formula.satisfies ξ φ := (Formula.satisfies_neg_iff ξ φ).mp
    ((forcing_truth_l L hN hU (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ) δ ξ hv).mp
      ⟨r, hrU, (forces_neg_l hE φ δ r).mpr hneg⟩)
  exact hnot (valid N hN η L names hpos' hne' ((tr α hα).mp hraw) U hU hpU ξ (fun i => hv (.bound i)))

end YesMetaZFC.Model.Forcing.Internal

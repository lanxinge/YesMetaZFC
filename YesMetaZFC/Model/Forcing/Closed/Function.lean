import YesMetaZFC.Model.Forcing.Internal.Functions.Decision
import YesMetaZFC.Model.Forcing.Closed.Basic

/-! # 可数闭力迫同时判定整个内部函数图

先对每个内部自然数决定旧值，再用内部可数稠密交获得统一条件。
同一条件上的唯一性允许替换收集整个旧函数图；所得见证仍由原公式定义。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def Old_fn_d (I : kpair_convention_l.Interpretation M) (B R z b f D X p : M.Domain) : Prop :=
  ∃ F, M.IsSetFunctionFromTo I F D X ∧
    ∀ i x, M.PairMember I i x F → Old_value_d M B R z b f p i x

def old_fn_m {n} (B R z b f D X p : Term n) : Formula 1 n :=
  .existsE (.conj (Formula.isFunctionFromTo kpair_convention_l .newest D.weaken X.weaken)
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest (.bound 2))
      (old_value_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        b.weaken.weaken.weaken f.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 1) .newest)))))
derive_free_closed old_fn_m

theorem old_fn_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n} (ρ : Env M n) (B R z b f D X p : Term n) :
    Formula.satisfies ρ (old_fn_m B R z b f D X p) ↔
      Old_fn_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (D.eval ρ) (X.eval ρ) (p.eval ρ) := by
  simp only [old_fn_m, Old_fn_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_orderedPairMem_iff I, old_value_sat_l hE, entry_m,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 在函数证书以下，决定全部内部 ω 坐标的实际旧函数图形成稠密集。 -/
theorem closed_fn_dense_l {ω a b T w f X} (hω : M.IsOmega ω) (hc : Closed_d I B R z ω)
    (h : Fn_name_d M B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b X w) :
    Dense_d M B R z (Old_fn_d I B R z b f ω X) a := by
  intro p hp
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f).push X
  let φ : BinarySchema 6 := {
    body := .existsE (.conj (.mem .newest (.bound 3))
      (old_value_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 2) .newest)) }
  have hφ i q : φ.denote ρ i q ↔ ∃ x, M.mem x X ∧ Old_value_d M B R z b f q i x := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, old_value_sat_l hZFC.1]
    rfl
  have hd i (hi : M.mem i ω) : Dense_d M B R z (φ.denote ρ i) p := by
    intro r hr
    obtain ⟨q, hq, hx⟩ := old_value_dense_l O hZF h hb ha hT hw hi r (below_trans_l O ha.1 hr hp)
    exact ⟨q, hq, (hφ i q).mpr hx⟩
  have hl i (_ : M.mem i ω) : Lower_d M B R z (φ.denote ρ i) := by
    intro r q hr hq hi
    obtain ⟨x, hx, hv⟩ := (hφ i r).mp hi
    exact (hφ i q).mpr ⟨x, hx, old_value_lower_l O hZF hb h.2.2.1 r q hr hq hv⟩
  obtain ⟨q, hq, hdec⟩ := closed_intersection_l O hZFC hω hc φ ρ hd hl hp.1 hp.2.1
  have hqa := below_trans_l O ha.1 hq hp
  have hqb := below_trans_l O hb hqa ha
  let ψ : BinarySchema 7 := {
    body := .conj (.mem .newest (.bound 3))
      (old_value_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1) .newest) }
  have hψ i x : ψ.denote (ρ.push q) i x ↔ M.mem x X ∧ Old_value_d M B R z b f q i x := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      old_value_sat_l hZFC.1]
    rfl
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ (ρ.push q)
    (source := ω) (target := X) (by
      intro i hi
      obtain ⟨x, hx⟩ := (hφ i q).mp (hdec i hi)
      exact ⟨x, (hψ i x).mpr hx⟩) (by
      intro i _ x y hx hy
      exact old_value_unique_l O hZF h ha.1 hb hqa hqb ((hψ i x).mp hx).2 ((hψ i y).mp hy).2)
    (fun i x _ hx => ((hψ i x).mp hx).1)
  exact ⟨q, hq, F, hF, fun i x hi => ((hψ i x).mp ((hf i x).mp hi).2).2⟩

end YesMetaZFC.Model.Forcing.Internal

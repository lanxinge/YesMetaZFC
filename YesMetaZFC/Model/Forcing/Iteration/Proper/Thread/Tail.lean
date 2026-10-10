import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Bounds
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Syntax
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 实际主前缀序列的任意共尾尾段

先在内部 ω 中截取指定指标之后的尾段，再按阶段重编号。全部前缀一致性消除
重复阶段的歧义；最小原像编号给出可数性，因此此步只需 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_tail_l {ω δ F G b D V N A γ E X Q j}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hc : M.IsCofinalNondecreasingOrdinalSequence I A ω γ)
    (hQ : M.IsSetFunctionFromTo I Q ω X) (hj : M.mem j ω)
    (hv : ∀ i x, Entry_d M i x Q → Row_pr_thread_d I F G b D N A i x)
    (hs : ∀ i k x y, M.SuccessorOf k i → Entry_d M i x Q → Entry_d M k y Q →
      Row_pr_advance_d I F G b D V N A E i x y) :
    ∃ J W, M.CardinalLessOrEqual I J ω ∧ Row_fusion_d I γ F J W ∧
      ∀ α p, Entry_d M α p W ↔ ∃ i x τ,
        (M.mem j i ∨ j = i) ∧ Entry_d M i α A ∧ Entry_d M i x Q ∧ KPair_d M x p τ := by
  have hA := hc.isSetFunctionFromTo
  have inc : Cc_increasing_d I A := by
    intro i k α β hik hi hk
    rcases hc.isNondecreasing.2 i (hA.input_mem_of_pairMember hi) k (hA.input_mem_of_pairMember hk) hik α β hi hk with he | hlt
    · exact he ▸ (fun _ h => h)
    · exact (hc.1.1.mem (hA.output_mem_of_pairMember hk)).transitive.memberSubset hlt
  have coh := row_pr_coherent_l hZF hω h hA inc hQ hv hs
  let η : Env M 1 := ⟨fun _ => j, fun _ => j⟩
  let θ : UnarySchema 1 := { body := .disj (.mem (.bound 1) .newest) (Formula.extensionalEq (.bound 1) .newest) }
  obtain ⟨L, hL'⟩ := ZF.separation_exists_d hZF θ η ω
  have hL i : M.mem i L ↔ M.mem i ω ∧ (M.mem j i ∨ j = i) := by
    simpa only [θ, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] using! hL' i
  obtain ⟨A', ha⟩ := ZF.exists_restriction hZF I A L
  have hA' := ha.isSetFunctionFromTo hA (fun i hi => ((hL i).mp hi).1)
  obtain ⟨J, hJ⟩ := ZF.exists_range_of_setFunction hZF I hA'.1 hA'.2.1
  have hAJ : M.IsSetFunctionFromTo I A' L J := ⟨hA'.1, hA'.2.1, fun i hi => by
    obtain ⟨α, _, hiα⟩ := hA'.2.2 i hi
    exact ⟨α, (hJ α).mpr ⟨i, hiα⟩, hiα⟩⟩
  obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I (fun i hi => ((hL i).mp hi).1)
  have hCount := ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF) ⟨f, hf⟩ hAJ (by
    intro α hα
    obtain ⟨i, hi⟩ := (hJ α).mp hα
    exact ⟨i, hA'.input_mem_of_pairMember hi, hi⟩)
  have sub α (hα : M.mem α J) : M.mem α γ := by
    obtain ⟨i, hi⟩ := (hJ α).mp hα
    exact hA'.output_mem_of_pairMember hi
  have cofinal z (hz : M.mem z γ) : ∃ α, M.mem α J ∧ M.mem z α := by
    obtain ⟨K, hK, hu⟩ := hc.isLimit.2.2
    obtain ⟨α, hα, hzα⟩ := (hu z).mp hz
    obtain ⟨i, hi⟩ := (hK α).mp hα
    have hiω := hA.input_mem_of_pairMember hi
    have pick k (hk : M.mem k ω) (hik : M.mem i k ∨ i = k) (hjk : M.mem j k ∨ j = k) :
        ∃ β, M.mem β J ∧ M.mem z β := by
      obtain ⟨β, _, hkβ⟩ := hA.2.2 k hk
      refine ⟨β, (hJ β).mpr ⟨k, (ha.2 k β).mpr ⟨(hL k).mpr ⟨hk, hjk⟩, hkβ⟩⟩, ?_⟩
      rcases hik with hik | rfl
      · exact inc i k α β hik hi hkβ z hzα
      · exact hA.1.2 i α β hi hkβ ▸ hzα
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare i hiω j hj with he | hij | hji
    · exact pick j hj (Or.inr (hZF.1.eq_of_same_members i j he)) (Or.inr rfl)
    · exact pick j hj (Or.inl hij) (Or.inr rfl)
    · exact pick i hiω (Or.inr rfl) (Or.inl hji)
  let ρ : Env M 3 := ((⟨fun _ => L, fun _ => L⟩ : Env M 1).push A).push Q
  let φ : BinarySchema 3 := {
    body := .existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound 7))
      (.conj (entry_m (.bound 2) (.bound 4) (.bound 6))
        (.conj (entry_m (.bound 2) (.bound 1) (.bound 5)) (kpair_m (.bound 1) (.bound 3) .newest)))))) }
  have hφ α p : φ.denote ρ α p ↔ ∃ i x τ, M.mem i L ∧ Entry_d M i α A ∧ Entry_d M i x Q ∧ KPair_d M x p τ := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, entry_sat_l M hZF.1, kpair_sat_l M hZF.1]
    rfl
  have total α (hα : M.mem α J) : ∃ p, φ.denote ρ α p := by
    obtain ⟨i, hi⟩ := (hJ α).mp hα
    obtain ⟨hiL, hiα⟩ := (ha.2 i α).mp hi
    obtain ⟨x, _, hx⟩ := hQ.2.2 i ((hL i).mp hiL).1
    obtain ⟨_, _, _, _, _, _, p, τ, _, hxp, _⟩ := hv i x hx
    exact ⟨p, (hφ α p).mpr ⟨i, x, τ, hiL, hiα, hx, hxp⟩⟩
  have unique α (_ : M.mem α J) p q (hp : φ.denote ρ α p) (hq : φ.denote ρ α q) : p = q := by
    obtain ⟨i, x, τ, _, hiα, hix, hxp⟩ := (hφ α p).mp hp
    obtain ⟨k, y, σ, _, hkα, hky, hyq⟩ := (hφ α q).mp hq
    have hpq := coh i k x y α α p τ q σ hix hky hiα hkα hxp hyq (fun _ h => h)
    have hqq := coh k k y y α α q σ q σ hky hky hkα hkα hyq hyq (fun _ h => h)
    exact hpq.eq hZF.1 hqq
  obtain ⟨Y, hY⟩ := ZF.exists_functionalImageOn hZF φ ρ J total unique
  obtain ⟨W, hW, hw⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun α p hα hp => (hY p).mpr ⟨α, hα, hp⟩)
  have edge α p : Entry_d M α p W ↔ ∃ i x τ,
      (M.mem j i ∨ j = i) ∧ Entry_d M i α A ∧ Entry_d M i x Q ∧ KPair_d M x p τ := by
    constructor
    · intro hp
      obtain ⟨i, x, τ, hi, hα, hx, hp⟩ := (hφ α p).mp ((hw α p).mp hp).2
      exact ⟨i, x, τ, ((hL i).mp hi).2, hα, hx, hp⟩
    · rintro ⟨i, x, τ, hi, hα, hx, hp⟩
      have hiL := (hL i).mpr ⟨hQ.input_mem_of_pairMember hx, hi⟩
      exact (hw α p).mpr ⟨(hJ α).mpr ⟨i, (ha.2 i α).mpr ⟨hiL, hα⟩⟩, (hφ α p).mpr ⟨i, x, τ, hiL, hα, hx, hp⟩⟩
  refine ⟨J, W, hCount, ⟨hW.1, hW.2.1, sub, cofinal, ?_, ?_⟩, edge⟩
  · intro α p hp
    obtain ⟨i, x, τ, _, hα, hx, hxp⟩ := (edge α p).mp hp
    obtain ⟨β, B, R, hβ, hB, _, p', τ', _, hxp', hpm, _⟩ := hv i x hx
    have he := hA.1.2 i β α hβ hα
    obtain ⟨hep, _⟩ := kpair_injective_l M hxp' hxp
    exact ⟨B, he ▸ hB, hep ▸ hpm.1⟩
  · intro α β p q hp hq hαβ
    obtain ⟨i, x, τ, _, hiα, hx, hxp⟩ := (edge α p).mp hp
    obtain ⟨k, y, σ, _, hkβ, hy, hyq⟩ := (edge β q).mp hq
    exact coh i k x y α β p τ q σ hx hy hiα hkβ hxp hyq hαβ

end YesMetaZFC.Model.Forcing.Internal

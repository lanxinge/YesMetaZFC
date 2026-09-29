import YesMetaZFC.Model.Forcing.CohenCoordinates
import YesMetaZFC.Model.Forcing.InternalCCCBounds
import YesMetaZFC.Model.Forcing.InternalChoice
import YesMetaZFC.Model.Forcing.InternalGeneric

/-! # 一次添加任意参数量的 Cohen 实数

Add(ω,κ) 的条件是 κ×ω 到二元集的内部有限部分函数。泛型并图的各行经分离与
替换组成扩张内的单射实数族；分行稠密集与对角稠密集分别保证互异性和新颖性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R : M.Domain} {U : M.Domain → Prop}
section
variable (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hU : Generic_d M B R B U)
local notation "E" => extension_l M (ZFC.models_zf_l hZFC) B R B U
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))
local notation "J" => kpair_interpretation_l E (extension_ext_l O (ZFC.models_zf_l hZFC) hU)
  (internal_pair_l O (ZFC.models_zf_l hZFC) hU)
include O hZFC hU

theorem cohen_family_l {ω κ P Y o l b} (hω : M.IsOmega ω) (hP : M.IsCartesianProduct I P κ ω)
    (hY : Pair_d M Y o l) (hol : o ≠ l)
    (hB : ∀ p, M.mem p B ↔ Fn_d I ω P Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (hb : U b) (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R B U s (e a)) :
    ∃ A H : (E).Domain, (E).IsPowerSetOf A (e ω) ∧ (E).IsSetInjectionFromTo J H (e κ) A ∧
      ∀ i, M.mem i κ → ∀ r, Entry_d E (e i) r H → ∀ a, r ≠ e a := by
  let hZF := ZFC.models_zf_l hZFC
  have hE := preserves_zfc_l O hZFC hU
  let hEZF := ZFC.models_zf_l hE
  obtain ⟨F, hF, hf⟩ := generic_function_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hEZF)) O hZF hU hb
    (fun hp => ((hB _).mp (hU.proper _ hp).1).1) (fun p q h => ((hR p q).mp h).2.2)
    (fun _ ha => fn_input_l O hZF hU hω hB hR ⟨o, (hY o).mpr (Or.inl rfl)⟩ ha) e hi he hv
  have edge {p a v} (hp : U p) (h : Entry_d M a v p) : Entry_d E (e a) (e v) F :=
    (hf (e a) (e v)).mpr ⟨p, hp, a, v, h, rfl, rfl⟩
  let δ : Env E 2 := (⟨fun _ => F, fun _ => F⟩ : Env E 1).push (e l)
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (kpair_m .newest (.bound 2) (.bound 1)) (entry_m .newest (.bound 3) (.bound 4))) }
  have hφ x n : φ.denote δ x n ↔ ∃ a, KPair_d E a x n ∧ Entry_d E a (e l) F := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l E hE.1, entry_sat_l E hE.1]
    rfl
  obtain ⟨A, hA, H, hH, hrow⟩ := ZF.fiber_function_l J hEZF φ δ (e κ) (e ω)
  have row {i r n a} (hr : Entry_d E (e i) r H) (hn : M.mem n ω) (ha : KPair_d M a i n) :
      e n ∈ r ↔ Entry_d E (e a) (e l) F := by
    constructor
    · intro hnr
      obtain ⟨v, hv, hvF⟩ := (hφ (e i) (e n)).mp (((hrow (e i) r).mp hr).2 (e n) |>.mp hnr).2
      exact kpair_unique_l E hE.1 hv (image_kpair_l e he ha) ▸ hvF
    · intro haF
      exact (((hrow (e i) r).mp hr).2 (e n)).mpr ⟨(image_member_l e hi he).mpr hn,
        (hφ (e i) (e n)).mpr ⟨e a, image_kpair_l e he ha, haF⟩⟩
  refine ⟨A, H, hA, ⟨hH, ?_⟩, ?_⟩
  · intro x y r hxr hyr
    obtain ⟨i, hiκ, rfl⟩ := (he κ x).mp (hH.input_mem_of_pairMember hxr)
    obtain ⟨j, hjκ, rfl⟩ := (he κ y).mp (hH.input_mem_of_pairMember hyr)
    classical
    by_cases hij : i = j
    · exact congrArg e hij
    · obtain ⟨p, hp, n, a, c, hn, ha, hc, hao, hcl⟩ := rows_split_l hZFC hU hω hP hY hB hR hiκ hjκ hij
      have hnR := (row hyr hn hc).mpr (edge hp hcl)
      exact False.elim (hol (hi (hF.1.2 (e a) (e o) (e l) (edge hp hao) ((row hxr hn ha).mp hnR))))
  · intro i hiκ r hr a heq
    obtain ⟨p, hp, n, c, hn, hc, hd⟩ := row_diagonal_l hZFC hU hω hP hY hB hR hiκ a
    rcases hd with ⟨hna, hco⟩ | ⟨hna, hcl⟩
    · have hnR : e n ∈ r := heq.symm ▸ (image_member_l e hi he).mpr hna
      exact hol (hi (hF.1.2 (e c) (e o) (e l) (edge hp hco) ((row hr hn hc).mp hnR)))
    · exact hna ((image_member_l e hi he).mp (heq ▸ (row hr hn hc).mpr (edge hp hcl)))

/-- 自动装配的结果只返回存在性证书，不选择全局不可计算的泛型或模型。 -/
def Cohen_result_d (ω κ : M.Domain) : Prop :=
  (E).Models ZFC ∧ ∃ b, U b ∧ ∃ e : M.Domain → (E).Domain,
    Function.Injective e ∧ (∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y) ∧
    (∀ a s, Check_d M b a s → Qval_d M B R B U s (e a)) ∧
    (E).IsOmega (e ω) ∧
    (∀ μ, M.IsInfiniteCardinal I ω μ → (E).IsInfiniteCardinal J (e ω) (e μ)) ∧
    ∃ A H : (E).Domain, (E).IsPowerSetOf A (e ω) ∧ (E).IsSetInjectionFromTo J H (e κ) A ∧
      ∀ i, M.mem i κ → ∀ r, Entry_d E (e i) r H → ∀ a, r ≠ e a

end

/-- 给定任意模型内指标集 κ，一次构造 Add(ω,κ)、可数链条件及互异新实数族。 -/
theorem cohen_forcing_l (M : SetTheory.Structure.{u}) (hZFC : M.Models ZFC) (κ : M.Domain) :
    ∃ ω B R, M.IsOmega ω ∧ ∃ O : Cond_order_d M B R B,
      (∃ p, M.mem p B ∧ p ≠ B) ∧
      Ccc_d M (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B ∧
      ∀ U, ∀ hU : Generic_d M B R B U, Cohen_result_d O hZFC hU ω κ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  obtain ⟨l, hl, hlω⟩ := hω.1.2 o hoω
  obtain ⟨Y, hY⟩ := KP.exists_pair (ZF.modelsKP hZF) o l
  have hol : o ≠ l := fun h => ho o (h.symm ▸ hl.predecessor_mem)
  have hYω : M.CardinalLessOrEqual I Y ω := ZF.exists_inclusionInjection hZF I (fun x hx =>
    ((hY x).mp hx).elim (fun h => h ▸ hoω) (fun h => h ▸ hlω))
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I κ ω
  obtain ⟨B, R, hB, hR, O, hc⟩ := fn_order_ccc_l M hZFC hω hYω P
  have hoB := (hB o).mpr (ZF.fn_empty_l I hZF hω ho)
  refine ⟨ω, B, R, hω, O, ⟨o, hoB, fun h => KP.mem_irrefl_d (ZF.modelsKP hZF) B (h ▸ hoB)⟩,
    hc, fun U hU => ⟨preserves_zfc_l O hZFC hU, ?_⟩⟩
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  have hE := preserves_zf_l O hZF hU
  have hωE := image_omega_l (hEN := hE.1) e hi he hZF (internal_foundation_l O hZF hU) hω
    (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  obtain ⟨A, H, hA, hH, hnew⟩ := cohen_family_l O hZFC hU hω hP hY hol hB hR hb e hi he hv
  exact ⟨b, hb, e, hi, he, hv, hωE, fun μ hμ => ccc_infinite_cardinal_l O hZFC hU hω hc hμ hb e hi he hv,
    A, H, hA, hH, hnew⟩

/-- 可数地模型上，添加量 κ 是唯一额外数学参数；偏序、泛型和实数族自动生成。 -/
theorem cohen_extension_l (M : SetTheory.Structure.{u}) (hZFC : M.Models ZFC) (κ : M.Domain)
    (e : Nat → M.Domain) (he : Function.Surjective e) :
    ∃ ω B R U, M.IsOmega ω ∧ ∃ O : Cond_order_d M B R B, ∃ hU : Generic_d M B R B U,
      Ccc_d M (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B ∧
        Cohen_result_d O hZFC hU ω κ := by
  obtain ⟨ω, B, R, hω, O, ⟨p, hp, hn⟩, hc, h⟩ := cohen_forcing_l M hZFC κ
  obtain ⟨U, hU, _⟩ := internal_generic_l O e he hp hn
  exact ⟨ω, B, R, U, hω, O, hU, hc, h U hU⟩

end YesMetaZFC.Model.Forcing.Internal

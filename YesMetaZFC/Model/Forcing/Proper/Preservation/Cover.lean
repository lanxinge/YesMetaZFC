import YesMetaZFC.Model.Forcing.Proper.Hereditary.Hull
import YesMetaZFC.Model.Forcing.Proper.Generic.Ground
import YesMetaZFC.Model.Forcing.Internal.Functions.Injection
import YesMetaZFC.Model.Forcing.Internal.Functions.Cover
import YesMetaZFC.SetTheory.Card.FiniteParameters

/-! # proper 力迫的实际旧可数覆盖名称

同一个可数初等 N 捕获单射名称及全部旧自然数。任意接受其主条件的泛型中，
名称的每个元素都属于 N[G]，其旧部分因而被 N∩X 覆盖。全泛型判据及有限参数
反射将这一事实变为原模型内真实的覆盖力迫，并给出稠密的覆盖见证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

private theorem countable_cover_l (e₀ : Nat → M.Domain) (he₀ : Function.Surjective e₀)
    {ω b X t u w f p} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z)
    (hb : M.mem b B) (hp : Below_d M B R z p b) (hu : Check_d M b X u) (hw : Check_d M b ω w)
    (hf : Inj_name_d M B R z p t w f) : ∃ q, Below_d M B R z q p ∧ Old_cover_d I ω B R z b X t u q := by
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) X ω
  obtain ⟨T, J, hT, hJ, hc⟩ := check_cover_l hZF b P
  obtain ⟨u', hu'⟩ := hc X (hT.1 P hT.2.1 X ((hP X).mpr (Or.inl rfl)))
  obtain ⟨w', hw'⟩ := hc ω (hT.1 P hT.2.1 ω ((hP ω).mpr (Or.inr rfl)))
  have heu := check_unique_l M hZF.1 (check_ind_l M hZF) b X u' u ⟨J, hJ, hu'⟩ hu
  have hew := check_unique_l M hZF.1 (check_ind_l M hZF) b ω w' w ⟨J, hJ, hw'⟩ hw
  subst u' w'
  let a : Fin 7 → M.Domain := Fin.cases B (Fin.cases R (Fin.cases z (Fin.cases J (Fin.cases X (Fin.cases ω (fun _ => f))))))
  obtain ⟨A, ha, hA⟩ := ZF.finite_params_l I hZF hω a
  obtain ⟨χ, H, c, S, N, d, K, q, hχ, hωχ, hH, hM, hSub, hElem, hAN, hn, hqp, hm, hg⟩ :=
    ng_hchi_hull_l O hZFC hω hPr (ZF.finite_countable_l I hZF hω ha) hp.1 hp.2.1
  have memN i : M.mem (a i) N := hAN _ ((hA _).mpr ⟨i, rfl⟩)
  obtain ⟨Y, hY⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) N X
  obtain ⟨g, hgN⟩ := ZF.exists_inclusionInjection hZF I (fun x hx => ((hY x).mp hx).1)
  obtain ⟨j, hj⟩ := hn
  have hCount := ZF.exists_compositionInjection hZF I hgN hj
  obtain ⟨s, hs, hsn, _⟩ := zf_check_l M hZF hb Y
  refine ⟨q, hqp, Y, s, (fun x hx => ((hY x).mp hx).2), hCount, hs, ?_⟩
  let ρ := cover_env_l t u s
  have hρ : ∀ i, Name_d M B (ρ.bound i) :=
    Fin.cases hsn (Fin.cases (check_name_l M (check_range_l M hZF) hb hu) (fun _ => hf.1))
  apply forces_countable_l O hZF e₀ he₀ cover_body_m cover_body_closed_l ρ hρ hqp.1 hqp.2.1
  intro U hU hq η hη
  have hpU := hU.upward q p hq hp.1 hqp.2.2
  have hbU := hU.upward p b hpU hb hp.2.2
  let E := extension_l M hZF B R z U
  let I' := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
  have hE := preserves_zf_l O hZF hU
  obtain ⟨_, H', Z, ω', c', S', d', K', _, _, _, _, _, _, hZ, hω', htr', _, hM', hSub', hElem'⟩ := hg U hU hq
  obtain ⟨e, hv, he, _⟩ := check_map_l O hZF hU hbU
  obtain ⟨F, hF⟩ := name_value_l (R := R) (z := z) (U := U) hf.2.2.1
  have hinj := inj_name_val_l O hZF hU hf hpU (hη 2) (hv ω w hw) hF
  have hFN : F ∈ Z := (hZ F).mpr ⟨f, memN 6, hF⟩
  have htr := ZF.h_transitive_l I hZF hH
  have hωN := selem_omega_subset_l I hM.2 htr hZF hω hSub hElem (memN 5)
  have fn i s t (hs : Entry_d M i s J) (ht : Entry_d M i t J) : s = t :=
    check_unique_l M hZF.1 (check_ind_l M hZF) b i s t ⟨J, hJ, hs⟩ ⟨J, hJ, ht⟩
  have hωZ i (hiω : M.mem i ω) : e i ∈ Z := by
    obtain ⟨v, hiv⟩ := (hJ.2 ω w hw').1 i hiω
    have hvN := selem_entry_value_l I hM.2 htr hZF hω hSub hElem (memN 3) (hωN i hiω) fn hiv
    exact (hZ (e i)).mpr ⟨v, hvN, hv i v ⟨J, hJ, hiv⟩⟩
  have hXe : e X = η.bound 1 := qval_unique_l (hv X u hu) (hη 1)
  have hYe : e Y = η.bound 0 := qval_unique_l (hv Y s hs) (hη 0)
  simp only [cover_body_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff]
  change ∀ x, x ∈ η.bound 2 → x ∈ η.bound 1 → x ∈ η.bound 0
  intro x hx hxX
  obtain ⟨v, hvω, hxv⟩ := hinj.1.2.2 x hx
  obtain ⟨i, hiω, rfl⟩ := (he ω v).mp hvω
  obtain ⟨y, hyZ, hyi⟩ := selem_entry_witness_l I' hM'.2 htr' hE hω' hSub' hElem' hFN (hωZ i hiω) ⟨x, hxv⟩
  have hxZ : x ∈ Z := hinj.2 y x (e i) hyi hxv ▸ hyZ
  obtain ⟨a, haN, haX, hax⟩ := (ng_ground_trace_l hZFC hω hχ hωχ hH hM.2 hSub hElem O hU
    (memN 0) (memN 1) (memN 2) (memN 3) (memN 4) hJ hu' hbU hm hq e hv x).mp
      ⟨(hZ x).mp hxZ, hXe.symm ▸ hxX⟩
  exact hYe ▸ (he Y x).mpr ⟨a, (hY a).mpr ⟨haN, haX⟩, hax⟩

/-- 任意可数名称在旧集合中的部分，都可在加强条件下由实际旧可数集覆盖。 -/
theorem proper_name_cover_l {ω b X t u w f p} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z)
    (hb : M.mem b B) (hp : Below_d M B R z p b) (hu : Check_d M b X u) (hw : Check_d M b ω w)
    (hf : Inj_name_d M B R z p t w f) : ∃ q, Below_d M B R z q p ∧ Old_cover_d I ω B R z b X t u q := by
  let ρ : Env M 11 := ((((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push ω).push b).push X).push t).push u).push w).push f).push p
  let φ : Formula 1 11 := .conj (cond_order_m (.bound 10) (.bound 9) (.bound 8))
    (.conj (Formula.isOmega (.bound 7)) (.conj (proper_m (.bound 7) (.bound 10) (.bound 9) (.bound 8))
    (.conj (.mem (.bound 6) (.bound 10)) (.conj (below_m (.bound 10) (.bound 9) (.bound 8) .newest (.bound 6))
    (.conj (check_m (.bound 6) (.bound 5) (.bound 3)) (.conj (check_m (.bound 6) (.bound 7) (.bound 2))
      (inj_name_m (.bound 10) (.bound 9) (.bound 8) .newest (.bound 4) (.bound 2) (.bound 1))))))))
  let ψ : Formula 1 11 := .existsE (.conj (below_m (.bound 11) (.bound 10) (.bound 9) .newest (.bound 1))
    (old_cover_m (.bound 8) (.bound 11) (.bound 10) (.bound 9) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest))
  have hφ : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed]
  have raw (V : SetTheory.Structure.{u}) (hV : V.Models ZFC) (η : Env V 11) : Formula.satisfies η φ ↔
      let J := kpair_interpretation_l V hV.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hV)))
      Cond_order_d V (η.bound 10) (η.bound 9) (η.bound 8) ∧ V.IsOmega (η.bound 7) ∧
      Proper_d J (η.bound 7) (η.bound 10) (η.bound 9) (η.bound 8) ∧ V.mem (η.bound 6) (η.bound 10) ∧
      Below_d V (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 6) ∧
      Check_d V (η.bound 6) (η.bound 5) (η.bound 3) ∧ Check_d V (η.bound 6) (η.bound 7) (η.bound 2) ∧
      Inj_name_d V (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 4) (η.bound 2) (η.bound 1) := by
    let J := kpair_interpretation_l V hV.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hV)))
    simp only [φ, Formula.satisfies_conj_iff, cond_order_sat_l hV.1, Formula.satisfies_isOmega_iff,
      proper_sat_l J hV.1, Formula.satisfies_mem_iff, below_sat_l V hV.1, check_sat_l V hV.1, inj_name_sat_l hV.1]
    rfl
  have result (V : SetTheory.Structure.{u}) (hV : V.Models ZFC) (η : Env V 11) : Formula.satisfies η ψ ↔
      let J := kpair_interpretation_l V hV.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hV)))
      ∃ q, Below_d V (η.bound 10) (η.bound 9) (η.bound 8) q (η.bound 0) ∧
        Old_cover_d J (η.bound 7) (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 3) q := by
    let J := kpair_interpretation_l V hV.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hV)))
    simp only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, below_sat_l V hV.1, old_cover_sat_l J hV.1]
    rfl
  apply (result M hZFC ρ).mp
  apply FirstOrderSemantics.countable_consequence_l (Γ := ZFC) φ ψ hφ hψ
    (fun V hV e he η hs => ?_) hZFC ρ ((raw M hZFC ρ).mpr ⟨O, hω, hPr, hb, hp, hu, hw, hf⟩)
  obtain ⟨O', hω', hPr', hb', hp', hu', hw', hf'⟩ := (raw V hV η).mp hs
  exact (result V hV η).mpr (countable_cover_l O' hV e he hω' hPr' hb' hp' hu' hw' hf')

theorem proper_cover_dense_l {ω b X t u w f p} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z)
    (hb : M.mem b B) (hp : Below_d M B R z p b) (hu : Check_d M b X u) (hw : Check_d M b ω w)
    (hf : Inj_name_d M B R z p t w f) : Dense_d M B R z (Old_cover_d I ω B R z b X t u) p := by
  let ρ := fn_env_l t w f
  have hρ : ∀ a : Term 3, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact hf.2.1
    | bound i => exact Fin.cases hf.2.2.1 (Fin.cases hf.1 (fun _ => hf.2.1)) i
  intro r hr
  have hf' : Inj_name_d M B R z r t w f := ⟨hf.1, hf.2.1, hf.2.2.1,
    (forces_regular_l O hZF inj_body_m ρ hρ).1 p r hp.1 hr hf.2.2.2⟩
  exact proper_name_cover_l O hZFC hω hPr hb (below_trans_l O hb hr hp) hu hw hf'

end YesMetaZFC.Model.Forcing.Internal

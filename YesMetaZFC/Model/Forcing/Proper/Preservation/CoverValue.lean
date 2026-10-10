import YesMetaZFC.Model.Forcing.Proper.Preservation.Cover

/-! # proper 泛型扩张中新可数集合的地模型覆盖

覆盖见证的存在性已在原模型中证明为稠密谓词，故给定的原泛型确实遇到它。
所选覆盖集属于地模型，并在地模型内部可数；无需改换泛型或假设额外闭性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem proper_countable_cover_l {ω b X} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
    (e : M.Domain → (E).Domain) (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    {Y : (E).Domain} (hc : (E).CardinalLessOrEqual J Y (e ω)) :
    ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ ∀ x, x ∈ Y → x ∈ e X → x ∈ e A := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨t, htn, ht⟩ := value_name_l Y
  obtain ⟨f, hfn, hf⟩ := value_name_l F
  obtain ⟨u, hu, _, _⟩ := zf_check_l M hZF (hU.proper b hb).1 X
  obtain ⟨w, hw, hwn, _⟩ := zf_check_l M hZF (hU.proper b hb).1 ω
  let ρ := fn_env_l t w f
  let η := fn_env_l Y (e ω) F
  have hρ : Env_val_d hZF ρ η := by
    intro s
    cases s with
    | free _ => exact hv ω w hw
    | bound i => exact Fin.cases hf (Fin.cases ht (fun _ => hv ω w hw)) i
  have hsat : Formula.satisfies η inj_body_m :=
    (Formula.satisfies_isInjectionFromTo_iff J (extension_ext_l O hZF hU) η .newest (.bound 1) (.bound 2)).mpr hF
  obtain ⟨p, hp, hforce⟩ := (forcing_truth_l O hZF hU inj_body_m inj_body_closed_l ρ η hρ).mpr hsat
  obtain ⟨r, hr, hrp, hrb⟩ := hU.directed p b hp hb
  have hr' := hU.proper r hr
  have hforce' := (forces_regular_l O hZF inj_body_m ρ (fun s => qval_name_l (hρ s))).1
    p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hforce
  have hi : Inj_name_d M B R z r t w f := ⟨htn, hwn, hfn, hforce'⟩
  let δ : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push R).push z).push b).push X).push t).push u
  let φ : UnarySchema 8 := {
    body := old_cover_m (.bound 8) (.bound 7) (.bound 6) (.bound 5)
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ q : φ.denote δ q ↔ Old_cover_d I ω B R z b X t u q :=
    old_cover_sat_l I hZFC.1 (δ.push q) _ _ _ _ _ _ _ _ _
  obtain ⟨q, hq, A, s, hAX, ha, hs, h⟩ := generic_pick_l hZF hU ⟨8, φ, δ, hφ⟩ hr
    (proper_cover_dense_l O hZFC hω hPr (hU.proper b hb).1 ⟨hr'.1, hr'.2, hrb⟩ hu hw hi)
  exact ⟨A, hAX, ha, cover_value_l O hZF hU hq h ht (hv X u hu) (hv A s hs)⟩

/-- 扩张中的每个新可数子集，均包含于地模型自己的某个可数子集。 -/
theorem proper_set_cover_l {ω b X} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
    (e : M.Domain → (E).Domain) (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    {Y : (E).Domain} (hY : (E).MemberSubset Y (e X)) (hc : (E).CardinalLessOrEqual J Y (e ω)) :
    ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ (E).MemberSubset Y (e A) := by
  obtain ⟨A, hAX, ha, h⟩ := proper_countable_cover_l O hZFC hU hω hPr hb e hv hc
  exact ⟨A, hAX, ha, fun x hx => h x hx (hY x hx)⟩

end YesMetaZFC.Model.Forcing.Internal

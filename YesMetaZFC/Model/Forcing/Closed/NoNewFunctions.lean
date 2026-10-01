import YesMetaZFC.Model.Forcing.Closed.Function
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 可数闭力迫不增加取值于旧集合的内部 ω 序列

原泛型遇到决定整个函数图的实际稠密集。统一条件产生的旧函数图与给定的
扩张函数逐点相等；无需外部枚举内部自然数，也无需更换泛型。
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
include O hU

/-- 任意旧目标集上的新 ω 函数，都有实际旧函数图作为规范嵌入原像。 -/
theorem no_new_functions_l {ω b X} (hω : M.IsOmega ω) (hc : Closed_d I B R z ω) (hb : U b)
    (e : M.Domain → (E).Domain) (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
    {F : (E).Domain} (hF : (E).IsSetFunctionFromTo J F (e ω) (e X)) :
    ∃ G, M.IsSetFunctionFromTo I G ω X ∧ e G = F := by
  have hbB := (hU.proper b hb).1
  obtain ⟨f, hfN, hf⟩ := value_name_l F
  obtain ⟨T, hT, hTN, _⟩ := zf_check_l M hZF hbB ω
  obtain ⟨w, hw, hwN, _⟩ := zf_check_l M hZF hbB X
  let ρ := fn_env_l T w f
  let η := fn_env_l (e ω) (e X) F
  have hρ : Env_val_d hZF ρ η := by
    intro t
    cases t with
    | free _ => exact hv X w hw
    | bound i => exact Fin.cases hf (Fin.cases (hv ω T hT) (fun _ => hv X w hw)) i
  have hsat : Formula.satisfies η fn_body_m :=
    (Formula.satisfies_isFunctionFromTo_iff J (extension_ext_l O hZF hU) η .newest (.bound 1) (.bound 2)).mpr hF
  obtain ⟨p, hp, hforce⟩ := (forcing_truth_l O hZF hU fn_body_m fn_body_closed_l ρ η hρ).mpr hsat
  obtain ⟨a, ha, hap, hab⟩ := hU.directed p b hp hb
  have ha' := hU.proper a ha
  have hfn : Fn_name_d M B R z a T w f := ⟨hTN, hwN, hfN,
    (forces_regular_l O hZF fn_body_m ρ (fn_env_names_l hTN hwN hfN)).1
      p a (hU.proper p hp).1 ⟨ha'.1, ha'.2, hap⟩ hforce⟩
  let δ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push f).push ω).push X
  let ψ : UnarySchema 7 := {
    body := old_fn_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hψ q : ψ.denote δ q ↔ Old_fn_d I B R z b f ω X q := old_fn_sat_l I hZFC.1 (δ.push q) _ _ _ _ _ _ _ _
  obtain ⟨q, hq, G, hG, hdec⟩ := generic_pick_l hZF hU ⟨7, ψ, δ, hψ⟩ ha
    (closed_fn_dense_l O hZFC hω hc hfn hbB ⟨ha'.1, ha'.2, hab⟩ hT hw)
  have hGF i x (hix : Entry_d M i x G) : Entry_d E (e i) (e x) F := by
    obtain ⟨s, hs, t, ht, hst⟩ := hdec i x hix
    exact (rel_force_truth_l O hZF hU (hv i s hs) (hv x t ht) hf).mp ⟨q, hq, hst⟩
  have hGe : (E).IsSetRelation J (e G) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := (he G t).mp ht
    obtain ⟨i, x, hs⟩ := hG.1.1 s hs
    exact ⟨e i, e x, image_kpair_l e he hs⟩
  refine ⟨G, hG, Structure.IsSetRelation.eq_of_pairMember_iff (extension_ext_l O hZF hU) hGe hF.1.1 ?_⟩
  intro i x
  constructor
  · intro hix
    obtain ⟨j, y, hjy, rfl, rfl⟩ := (image_entries_l e he hG.1.1 i x).mp hix
    exact hGF j y hjy
  · intro hix
    obtain ⟨j, hj, rfl⟩ := (he ω i).mp (hF.input_mem_of_pairMember hix)
    obtain ⟨y, _, hjy⟩ := hG.2.2 j hj
    have hxy := hF.1.2 (e j) x (e y) hix (hGF j y hjy)
    exact (image_entries_l e he hG.1.1 (e j) x).mpr ⟨j, y, hjy, rfl, hxy.symm⟩

end YesMetaZFC.Model.Forcing.Internal

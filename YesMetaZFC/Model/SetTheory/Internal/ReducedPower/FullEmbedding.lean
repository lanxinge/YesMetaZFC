import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Los
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Constant
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullProjection

/-! # 完整函数族上任意关系的常值与投影初等性

把代表赋值转置成逐点赋值，再对真实内部代码应用 Łoś。源关系可以包含
外部集合谓词；完整函数族必须由实际闭性证明给出，不能替换原代表族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}}

section Matrix
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rp_matrix_l {ω D X G E a : M.Domain}
    (hG : M.IsFunctionSpace I G D X) (hE : M.IsFunctionSpace I E ω X)
    (ha : M.IsSetFunctionFromTo I a ω G) :
    ∃ V, M.IsSetFunctionFromTo I V D E ∧ ∀ v f, Rd_entry_d v f V → Rp_column_d I ω a v f := by
  let ρ := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push a).push E
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 2)) (rp_column_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have sat v f : φ.denote ρ v f ↔ M.mem f E ∧ Rp_column_d I ω a v f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      rp_column_sat_l I hZF.1]; rfl
  obtain ⟨V, hV, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := E)
    (fun v hv => by
      obtain ⟨f, hf, hc⟩ := rp_column_exists_l I hZF hG ha hv
      exact ⟨f, (sat v f).mpr ⟨(hE f).mpr (fn0_function_l (ZF.modelsKP hZF) hf), hc⟩⟩)
    (fun v _ f g hf hg => rp_column_unique_l I hZF.1 ha
      (fn0_of_function_l (ZF.modelsKP hZF) ((hE f).mp ((sat v f).mp hf).1))
      (fn0_of_function_l (ZF.modelsKP hZF) ((hE g).mp ((sat v g).mp hg).1))
      ((sat v f).mp hf).2 ((sat v g).mp hg).2)
    (fun v f _ hf => ((sat v f).mp hf).1)
  exact ⟨V, hV, fun v f hv => ((sat v f).mp ((spec v f).mp hv).2).2⟩

end Matrix
section Elementary
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rp_full_constant_l {ω D X U R c d G p C T j : M.Domain}
    (hω : M.IsOmega ω) (hU : Maximal_d (ℳ := M) D U) (hs : Smdl_d I c X R)
    (hm : Rp_model_d I D X U R d G p C T) (hG : ∀ f, Fn0_d D X f → M.mem f G)
    (hj : M.IsSetInjectionFromTo I j X C)
    (spec : ∀ x B, Rd_entry_d x B j ↔ M.mem x X ∧ ∃ f,
      M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B p) : Smap_d I ω c d X C j := by
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨hj, A, hA, fun z f e hz hf he hfe => ?_⟩
  obtain ⟨V, hV, vs⟩ := ZF.exists_constantFunction hZF I (source := D) ((hE f).mpr hf)
  have eval : Rp_eval_d I ω D p V e := by
    intro i hi
    obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
    obtain ⟨B, _, hxB⟩ := hj.1.2.2 x hx
    obtain ⟨_, g, hg, hc, hp⟩ := (spec x B).mp hxB
    refine ⟨g, B, hp, hfe i hi x B hix hxB, fun v hv w hvw y => ?_⟩
    have eq := ((vs v w).mp hvw).2
    subst w
    exact ⟨fun hgy => (fn0_function_l (ZF.modelsKP hZF) (hm.map.functions g hg)).1.2 v y x hgy (hc v hv) ▸ hix,
      fun hiy => hf.1.2 i y x hiy hix ▸ hc v hv⟩
  have los := rp_satisfies_l I hZFC hU hm hG hs hA hE hV he eval hz
  refine ⟨fun ht => los.mpr ⟨D, hU.1.2.1, fun v hv => ⟨f, (vs v f).mpr ⟨hv, rfl⟩, ht⟩⟩, fun ht => ?_⟩
  obtain ⟨B, hB, hb⟩ := los.mp ht
  obtain ⟨v, hv⟩ := hU.2.1 B hB
  obtain ⟨g, hvg, ht⟩ := hb v hv
  exact ((vs v g).mp hvg).2 ▸ ht

theorem rp_full_embedding_l
    {ω X R s D E P Q U V t c d F G p q C N S T K j : M.Domain}
    (hω : M.IsOmega ω) (hs : Smdl_d I s X R) (hP : M.IsPowerSetOf P D)
    (hU : Maximal_d (ℳ := M) D U) (hV : Maximal_d (ℳ := M) E V) (ht : Push_d D E P Q U V t)
    (hp : Rp_model_d I D X U R c F p C S) (hq : Rp_model_d I E X V R d G q N T)
    (hF : ∀ f, Fn0_d D X f → M.mem f F) (hG : ∀ f, Fn0_d E X f → M.mem f G)
    (hK : M.IsSetFunctionFromTo I K F G) (hk : ∀ f g, Rd_entry_d f g K → Cp0_d E D X t f g)
    (hj : M.IsSetInjectionFromTo I j C N) (lift : Rp_lift_d I K p q j) : Smap_d I ω c d C N j := by
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨H, hH⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨hj, A, hA, fun z e₀ e₁ hz he₀ he₁ hh => ?_⟩
  obtain ⟨a, ha, eval⟩ := rp_representatives_l I hZFC hp.map he₀
  have hF' : M.IsFunctionSpace I F D X := fun f =>
    ⟨fun hf => fn0_function_l (ZF.modelsKP hZF) (hp.map.functions f hf),
      fun hf => hF f (fn0_of_function_l (ZF.modelsKP hZF) hf)⟩
  obtain ⟨W, hW, col⟩ := rp_matrix_l hZF hF' hH ha
  obtain ⟨W', hW', comp⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) ht.1) hW
  have r₀ : Rp_eval_d I ω D p W e₀ := by
    intro i hi
    obtain ⟨f, hf, hif⟩ := ha.2.2 i hi
    obtain ⟨B, _, hfB⟩ := hp.map.projection.2.2 f hf
    exact ⟨f, B, hfB, eval i hi f B hif hfB, fun v _ w hvw x => (col v w hvw i hi f hif x).symm⟩
  have r₁ : Rp_eval_d I ω E q W' e₁ := by
    intro i hi
    obtain ⟨f, hf, hif⟩ := ha.2.2 i hi
    obtain ⟨B, _, hfB⟩ := hp.map.projection.2.2 f hf
    obtain ⟨g, hg, hfg⟩ := hK.2.2 f hf
    obtain ⟨Z, _, hgZ⟩ := hq.map.projection.2.2 g hg
    refine ⟨g, Z, hgZ, hh i hi B Z (eval i hi f B hif hfB) (lift f g B Z hfg hfB hgZ), ?_⟩
    intro v _ w hvw x
    obtain ⟨_, u, hvu, huw⟩ := (comp v w).mp hvw
    exact ((hk f g hfg).value_l ht.1 (hp.map.functions f hf) hvu).trans
      (col u w huw i hi f hif x).symm
  let ρ := (((⟨fun _ => W, fun _ => W⟩ : Env M 1).push ω).push s).push z
  let φ : UnarySchema 4 := {
    body := .existsE (.conj (rd_entry_m (.bound 1) .newest (.bound 5))
      (satisfies_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 3) (.bound 2) .newest)) }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF φ ρ D
  have read v : M.mem v B ↔ M.mem v D ∧ ∃ f, Rd_entry_d v f W ∧ Satisfies_d I ω s z f := by
    simpa only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, satisfies_sat_l I hZF.1] using! bs v
  obtain ⟨B', _, pull, measure⟩ := ht.2 B ((hP B).mpr fun v hv => ((read v).mp hv).1)
  have read' v : M.mem v B' ↔ M.mem v E ∧ ∃ f, Rd_entry_d v f W' ∧ Satisfies_d I ω s z f := by
    refine (pull v).trans ⟨?_, ?_⟩
    · rintro ⟨hv, u, hu, hvu⟩
      obtain ⟨_, f, huf, hf⟩ := (read u).mp hu
      exact ⟨hv, f, (comp v f).mpr ⟨hv, u, hvu, huf⟩, hf⟩
    · rintro ⟨hv, f, hvf, hf⟩
      obtain ⟨_, u, hvu, huf⟩ := (comp v f).mp hvf
      exact ⟨hv, u, (read u).mpr ⟨(ht.1.bound_l hvu).2, f, huf, hf⟩, hvu⟩
  have truth {D U B : M.Domain} (hU : Maximal_d (ℳ := M) D U) (ψ : M.Domain → Prop)
      (read : ∀ v, M.mem v B ↔ M.mem v D ∧ ψ v) :
      M.mem B U ↔ ∃ Z, M.mem Z U ∧ ∀ v, M.mem v Z → ψ v := by
    refine ⟨fun h => ⟨B, h, fun v hv => ((read v).mp hv).2⟩, ?_⟩
    rintro ⟨Z, hz, hh⟩
    exact hU.1.2.2.1 Z B hz (fun v hv => (read v).mpr ⟨hU.1.1 Z hz v hv, hh v hv⟩)
      (fun v hv => ((read v).mp hv).1)
  have los₀ := rp_satisfies_l I hZFC hU hp hF hs hA hH hW he₀ r₀ hz
  have los₁ := rp_satisfies_l I hZFC hV hq hG hs hA hH hW' he₁ r₁ hz
  exact los₀.trans ((truth hU _ read).symm.trans (measure.symm.trans ((truth hV _ read').trans los₁.symm)))

end Elementary
end YesMetaZFC.SetTheory.Internal

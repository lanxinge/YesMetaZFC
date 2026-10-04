import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource

/-! # 全部有限支撑源分量的统一模型图

每个分量都以源中的函数族形成规范等价类。规范性给出结构码唯一性，随后
一次替换生成整个模型图；不逐分量选择模型，也不加入外部函数代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ep_component_d (ω κ L X R F a c : M.Domain) : Prop := ∃ n D U G p C T,
  M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
  (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R c G p C T

def ep_component_m {d} (ω κ L X R F a c : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+7) := x.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 6) (w ω)) (.conj (fn0_m (.bound 6) (w L) (w a))
      (.conj (ep_space_m (w κ) (.bound 6) (.bound 5)) (.conj (rd_entry_m (w a) (.bound 4) (w F))
        (.conj (.forallE (.iff (.mem .newest (.bound 4)) (.conj (.mem .newest (w X).weaken)
          (fn0_m (.bound 6) (w X).weaken .newest))))
          (rp_model_m (𝒞 := kpair_convention_l) (.bound 5) (w X) (.bound 4) (w R) (w c)
            (.bound 3) (.bound 2) (.bound 1) .newest))))))))))))
derive_free_closed ep_component_m

theorem ep_component_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L X R F a c : Term d) :
    Formula.satisfies ρ (ep_component_m ω κ L X R F a c) ↔
      Ep_component_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (F.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [ep_component_m, Ep_component_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, ep_space_sat_l hE, rd_entry_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rp_model_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ep_component_unique_l (hE : Extensional M) {ω κ L X R F a c d : M.Domain}
    (hF : Em_family_d ω κ L F) (hc : Ep_component_d I ω κ L X R F a c)
    (hd : Ep_component_d I ω κ L X R F a d) : c = d := by
  obtain ⟨n, D, U, G, p, C, T, _, hn, hD, haU, hG, hm⟩ := hc
  obtain ⟨n', D', U', G', p', C', T', _, hn', hD', haU', hG', hm'⟩ := hd
  have e := hn'.domain_eq_l hE hn
  subst n'
  have e := hE.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  have e := hF.function a U' U haU' haU
  subst U'
  have e := hE.eq_of_same_members G' G (fun f => (hG' f).trans (hG f).symm)
  subst G'
  have ep := hm'.map.projection.1.1.eq_of_pairMember_iff hE hm.map.projection.1.1
    (fun f B => (hm'.map.classes f B).trans (hm.map.classes f B).symm)
  subst p'
  have ec := hE.eq_of_same_members C' C (fun B => (hm'.map.range B).trans (hm.map.range B).symm)
  subst C'
  have et : T' = T := by
    apply hm'.code.2.2.1.eq_of_pairMember_iff hE hm.code.2.2.1
    intro B E
    have transfer {c₀ c₁ S₀ S₁} (h₀ : Rp_model_d I D X U R c₀ G p C S₀)
        (h₁ : Rp_model_d I D X U R c₁ G p C S₁) (hBD : M.PairMember I B E S₀) : M.PairMember I B E S₁ := by
      obtain ⟨f, hf⟩ := (h₀.map.range B).mp ((h₀.code.2.2.2 B E hBD).1)
      obtain ⟨g, hg⟩ := (h₀.map.range E).mp ((h₀.code.2.2.2 B E hBD).2)
      exact (h₁.relation f g B E hf hg).mpr ((h₀.relation f g B E hf hg).mp hBD)
    exact ⟨transfer hm' hm, transfer hm hm'⟩
  subst T'
  exact I.unique hm.code.1 hm'.code.1

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_components_l {ω κ K L X R F J : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hF : Em_family_d ω κ L F)
    (hJ : ∀ a, M.mem a J → ∃ n, M.mem n ω ∧ Fn0_d n L a) : ∃ Z Q, Fn0_d J Q Z ∧
      ∀ a c, Rd_entry_d a c Z → Ep_component_d Kp ω κ L X R F a c := by
  let ρ := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push κ).push L).push X).push R).push F
  let φ : BinarySchema 6 := {
    body := ep_component_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a c : φ.denote ρ a c ↔ Ep_component_d Kp ω κ L X R F a c := ep_component_sat_l Kp hZF.1 _ _ _ _ _ _ _ _ _
  have total a (ha : M.mem a J) : ∃ c, φ.denote ρ a c := by
    obtain ⟨n, hn, hna⟩ := hJ a ha
    obtain ⟨U, haU⟩ := hF.total n a hn hna
    obtain ⟨n', D, _, hna', hD, hU⟩ := hF.measure a U haU
    have en := hna'.domain_eq_l hZF.1 hna
    subst n'
    obtain ⟨G, c, p, C, T, hG, hm⟩ := h.model_l hZFC hn hD hU.1.base_l
    exact ⟨c, (sat a c).mpr ⟨n, D, U, G, p, C, T, hn, hna, hD, haU, hG, hm⟩⟩
  have unique a (_ : M.mem a J) c d hc hd := ep_component_unique_l Kp hZF.1 hF ((sat a c).mp hc) ((sat a d).mp hd)
  obtain ⟨Q, hQ⟩ := ZF.exists_functionalImageOn hZF φ ρ J total unique
  obtain ⟨Z, hz, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ ρ total unique
    (fun a c ha hc => (hQ c).mpr ⟨a, ha, hc⟩)
  exact ⟨Z, Q, fn0_of_function_l (ZF.modelsKP hZF) hz, fun a c hc => (sat a c).mp ((spec a c).mp hc).2⟩

end YesMetaZFC.SetTheory.LargeCardinal

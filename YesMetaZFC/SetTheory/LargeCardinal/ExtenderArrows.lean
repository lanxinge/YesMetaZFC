import YesMetaZFC.SetTheory.LargeCardinal.ExtenderComponents
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullElementary

/-! # 全系统过渡映射的统一图公式

类之间的箭头以类中代表的坐标拉回表达。任意代表都能实现同一箭头；因此
后续恒等、复合证明不必为不同分量选择一致的代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ep_arrow_d (ω κ L X a b B C : M.Domain) : Prop := ∃ m n q f g,
  M.mem m ω ∧ M.mem n ω ∧ Fn0_d m n q ∧ Fn0_d n L b ∧ Cp0_d m n L q b a ∧
  M.mem f B ∧ M.mem g C ∧ Ep_pull_d κ X m n q f g

def ep_arrow_m {d} (ω κ L X a b B C : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+5) := x.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4) (w ω))
    (.conj (.mem (.bound 3) (w ω)) (.conj (fn0_m (.bound 4) (.bound 3) (.bound 2))
      (.conj (fn0_m (.bound 3) (w L) (w b)) (.conj (cp0_m (.bound 4) (.bound 3) (w L) (.bound 2) (w b) (w a))
        (.conj (.mem (.bound 1) (w B)) (.conj (.mem .newest (w C))
          (ep_pull_m (w κ) (w X) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))))
derive_free_closed ep_arrow_m

theorem ep_arrow_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L X a b B C : Term d) :
    Formula.satisfies ρ (ep_arrow_m ω κ L X a b B C) ↔
      Ep_arrow_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (a.eval ρ) (b.eval ρ) (B.eval ρ) (C.eval ρ) := by
  simp only [ep_arrow_m, Ep_arrow_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, cp0_sat_l hE, ep_pull_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ep_map_l (hZFC : M.Models ZFC) {ω κ K L X R F a b c d m n q : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hco : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (hm : M.mem m ω) (hn : M.mem n ω) (hq : Fn0_d m n q) (hb : Fn0_d n L b)
    (hinj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j) (hqa : Cp0_d m n L q b a)
    (haM : Ep_component_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F a c)
    (hbM : Ep_component_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F b d) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ j C S E T, Smdl_d I c C S ∧ Smdl_d I d E T ∧ M.IsSetInjectionFromTo I j C E ∧
      Smap_d I ω c d C E j ∧
      (∀ B D B' D', Rd_entry_d B B' j → Rd_entry_d D D' j → (Rd_entry_d B D S ↔ Rd_entry_d B' D' T)) ∧
      (∀ B D, Rd_entry_d B D j ↔ M.mem B C ∧ M.mem D E ∧ Ep_arrow_d ω κ L X a b B D) ∧
      ∀ B D, Rd_entry_d B D j → ∀ f, M.mem f B → ∃ g, M.mem g D ∧ Ep_pull_d κ X m n q f g := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨m', D₀, U, G₀, p₀, C, S, _, ha, hD₀, haU, hG₀, hM₀⟩ := haM
  obtain ⟨n', D₁, V, G₁, p₁, E, T, _, hb', hD₁, hbV, hG₁, hM₁⟩ := hbM
  have em := ha.domain_eq_l hZF.1 hqa.1
  subst m'
  have en := hb'.domain_eq_l hZF.1 hb
  subst n'
  have hU := hF.at_l hZF.1 haU ha hD₀
  have hV := hF.at_l hZF.1 hbV hb hD₁
  obtain ⟨t, P, htX, ht, ts, hp, ps⟩ := h.family_l hZF hm hn hq hD₀ hD₁ hG₀ hG₁
  obtain ⟨c₀, hm₀⟩ := h.code
  obtain ⟨Q₀, U', hQ₀, hu, us, model₀⟩ := rs_restrict_model_l hZF h.omega h.transitive hm₀ h.theory
    (h.space_mem_l hZF hm hD₀) hU hG₀ hM₀
  obtain ⟨Q₁, V', hQ₁, hv, vs, model₁⟩ := rs_restrict_model_l hZF h.omega h.transitive hm₀ h.theory
    (h.space_mem_l hZF hn hD₁) hV hG₁ hM₁
  have push : Push_d D₀ D₁ Q₀ Q₁ U' V' t := ⟨ht, fun A hA => by
    obtain ⟨B, hBX, bs⟩ := sc_pull_l I hZF h.omega h.transitive hm₀ h.theory
      (h.space_mem_l hZF hn hD₁) htX ((hQ₀ A).mp hA).1
    have hBQ := (hQ₁ B).mpr ⟨hBX, fun s hs => ((bs s).mp hs).1⟩
    obtain ⟨B', hB', eq⟩ := hco m n q b a U V A hm hn ((hQ₀ A).mp hA).1 hq hb hqa hbV haU
      (fun r hr => (hD₀ r).mp (((hQ₀ A).mp hA).2 r hr))
    have eB : B' = B := hZF.1.eq_of_same_members B' B fun s => (hB' s).trans
      ⟨fun ⟨hs, r, hr, hsr⟩ => (bs s).mpr ⟨(hD₁ s).mpr hs, r, hr, (ts s r).mpr ⟨(hD₁ s).mpr hs, hsr⟩⟩,
        fun hs => by
          obtain ⟨hs, r, hr, hsr⟩ := (bs s).mp hs
          exact ⟨(hD₁ s).mp hs, r, hr, ((ts s r).mp hsr).2⟩⟩
    subst B'
    have vr : M.mem B V' ↔ M.mem B V := (vs B).trans ⟨And.right, fun h => ⟨hBQ, h⟩⟩
    have ur : M.mem A U' ↔ M.mem A U := (us A).trans ⟨And.right, fun h => ⟨hA, h⟩⟩
    exact ⟨B, hBQ, bs, vr.trans (eq.trans ur.symm)⟩⟩
  obtain ⟨P', j, hp', ps', elem, lift⟩ := rs_projection_embedding_l hZFC h.omega h.transitive hm₀ h.theory
    (h.space_mem_l hZF hm hD₀) (h.space_mem_l hZF hn hD₁) htX hQ₀ hQ₁ hu hv push hG₀ hG₁ model₀ model₁
  have eqP := hp'.1.1.eq_of_pairMember_iff hZF.1 hp.1.1 (fun f g => (ps' f g).trans (ps f g).symm)
  subst P'
  have hj := elem.1
  have rel B D B' D' (hb : Rd_entry_d B B' j) (hd : Rd_entry_d D D' j) :=
    elem.relation_l I hZF h.omega hM₀.code hM₁.code hb hd
  have pull f g (hfg : Rd_entry_d f g P) : Ep_pull_d κ X m n q f g :=
    ep_pull_of_comp_l hD₀ hD₁ ht (hM₀.map.functions f (hp.input_mem_of_pairMember hfg)) ts ((ps f g).mp hfg).2.2
  have any B D (hBD : Rd_entry_d B D j) f (hf : M.mem f B) : ∃ g, M.mem g D ∧ Ep_pull_d κ X m n q f g := by
    have hfp := hM₀.map.member_l I hZF.1 hU.base (hj.1.input_mem_of_pairMember hBD) hf
    obtain ⟨g, hg, hfg⟩ := hp.2.2 f (hM₀.map.projection.input_mem_of_pairMember hfp)
    obtain ⟨D', _, hgp⟩ := hM₁.map.projection.2.2 g hg
    have e := hj.1.1.2 B D' D (lift f g B D' hfg hfp hgp) hBD
    exact ⟨g, e ▸ hM₁.map.representative_l I hV.base hgp, pull f g hfg⟩
  refine ⟨j, C, S, E, T, hM₀.code, hM₁.code, hj, elem, rel, fun B D => ⟨?_, ?_⟩, any⟩
  · intro hBD
    have hBC := hj.1.input_mem_of_pairMember hBD
    obtain ⟨f, hf⟩ := (hM₀.map.range B).mp hBC
    have hff := hM₀.map.representative_l I hU.base hf
    obtain ⟨g, hg, hfg⟩ := any B D hBD f hff
    exact ⟨hBC, hj.1.output_mem_of_pairMember hBD, m, n, q, f, g, hm, hn, hq, hb, hqa, hff, hg, hfg⟩
  · rintro ⟨hBC, hDE, m', n', q', f, g, _, _, hq', hb', hqa', hfB, hgD, hfg⟩
    have en := hb'.domain_eq_l hZF.1 hb
    subst n'
    have em := hqa'.1.domain_eq_l hZF.1 ha
    subst m'
    have eq := ec_factor_unique_l hZF.1 hinj hq' hq hqa' hqa
    subst q'
    have hfp := hM₀.map.member_l I hZF.1 hU.base hBC hfB
    have hgp := hM₁.map.member_l I hZF.1 hV.base hDE hgD
    obtain ⟨g', _, hfg'⟩ := hp.2.2 f (hM₀.map.projection.input_mem_of_pairMember hfp)
    have eg := ep_pull_unique_l (ZF.modelsKP hZF) hq (pull f g' hfg') hfg
    exact lift f g B D (eg ▸ hfg') hfp hgp

end YesMetaZFC.SetTheory.LargeCardinal

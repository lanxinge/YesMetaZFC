import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.Filter.Countable
import YesMetaZFC.Model.SetTheory.ReducedPower.Overview
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Truncation

/-! # 完备测度的源分量内部良基

对任意源函数族，只用原完整测度的可数完备性。假设商有下降链，将相邻关系
写成唯一的完整真值集合，取其可数交，再在交中的一点求值，得到源关系的下降链。
源代数无须包含这些背景真值集合；也不需要对代表元或测度成员作可数选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 已构造的 κ 完备真测度自动提供精确的可数交接口。 -/
theorem ed_countable_l {ω κ D U : M.Domain} (hωκ : M.mem ω κ)
    (hp : FilterZF.Proper_d (ℳ := M) U) (hc : Ed_complete_d κ D U) : FilterZF.Cc_d ω D U := by
  intro F hF
  obtain ⟨E, hEU, he⟩ := hc ω hωκ F hF
  obtain ⟨v, hv⟩ := hp E hEU
  exact ⟨v, ((he v).mp hv).1, fun n B hn hnB => ((he v).mp hv).2 n hn B (hF.bound_l hnB).2 hnB⟩

def Ew_down_d (R a n v : M.Domain) : Prop := ∃ m f g x y, M.SuccessorOf m n ∧
  Rd_entry_d n f a ∧ Rd_entry_d m g a ∧ Rd_entry_d v x f ∧ Rd_entry_d v y g ∧ Rd_entry_d y x R

def ew_down_m {d} (R a n v : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (Formula.isSuccessor (.bound 4) n.weaken.weaken.weaken.weaken.weaken) (.conj
    (rd_entry_m n.weaken.weaken.weaken.weaken.weaken (.bound 3) a.weaken.weaken.weaken.weaken.weaken) (.conj
      (rd_entry_m (.bound 4) (.bound 2) a.weaken.weaken.weaken.weaken.weaken) (.conj
        (rd_entry_m v.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 3)) (.conj
          (rd_entry_m v.weaken.weaken.weaken.weaken.weaken .newest (.bound 2))
          (rd_entry_m .newest (.bound 1) R.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed ew_down_m

theorem ew_down_sat_l (hE : Extensional M) {d} (ρ : Env M d) (R a n v : Term d) :
    Formula.satisfies ρ (ew_down_m R a n v) ↔ Ew_down_d (R.eval ρ) (a.eval ρ) (n.eval ρ) (v.eval ρ) := by
  simp only [ew_down_m, Ew_down_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ew_down_value_l (hE : Extensional M) {ω D X G R a n m f g v x y : M.Domain}
    (ha : Fn0_d ω G a) (hG : ∀ f, M.mem f G → Fn0_d D X f) (hm : M.SuccessorOf m n)
    (hnf : Rd_entry_d n f a) (hmg : Rd_entry_d m g a) (hvx : Rd_entry_d v x f) (hvy : Rd_entry_d v y g) :
    Ew_down_d R a n v ↔ Rd_entry_d y x R := by
  refine ⟨?_, fun hr => ⟨m, f, g, x, y, hm, hnf, hmg, hvx, hvy, hr⟩⟩
  rintro ⟨m', f', g', x', y', hm', hnf', hmg', hvx', hvy', hr⟩
  have e : m' = m := hE.eq_of_same_members m' m fun z => (hm' z).trans (hm z).symm
  subst m'
  have e := ha.2.2 n (ha.bound_l hnf).1 f' (ha.bound_l hnf').2 f (ha.bound_l hnf).2 hnf' hnf
  subst f'
  have e := ha.2.2 m (ha.bound_l hmg).1 g' (ha.bound_l hmg').2 g (ha.bound_l hmg).2 hmg' hmg
  subst g'
  have hf := hG f (ha.bound_l hnf).2
  have hg := hG g (ha.bound_l hmg).2
  have e := hf.2.2 v (hf.bound_l hvx).1 x' (hf.bound_l hvx').2 x (hf.bound_l hvx).2 hvx' hvx
  have e' := hg.2.2 v (hg.bound_l hvy).1 y' (hg.bound_l hvy').2 y (hg.bound_l hvy).2 hvy' hvy
  exact e ▸ e' ▸ hr

/-- 完整滤子的可数交性质传到任意源函数族上的关系商；所需选择仅为 DC。 -/
theorem rp_wf_l (hZF : M.Models ZF) {ω D X U V R c G q C S : M.Domain}
    (hω : M.IsOmega ω) (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (hU : FilterZF.IsFilter_d (ℳ := M) D U) (hc : FilterZF.Cc_d ω D U)
    (hVU : M.MemberSubset V U) (hw : Wf_rel_d X R)
    (h : Rp_model_d (kp_pair_l (ZF.modelsKP hZF)) D X V R c G q C S) : Wf_rel_d C S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := ((⟨fun _ => X, fun _ => X⟩ : Env M 1).push V).push R
  let φ : BinarySchema 3 := {
    body := rp_rel_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, _, hp⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ G
  have hP f g : Rd_entry_d f g P ↔ M.mem f G ∧ M.mem g G ∧ Rp_rel_d I X V R f g :=
    (hp f g).trans (and_congr_right fun _ => and_congr_right fun _ => rp_rel_sat_l I hZF.1 _ _ _ _ _ _)
  have fnq := fn0_of_function_l (ZF.modelsKP hZF) h.map.projection
  apply (wf_quotient_l hZF fnq (fun B hB => (h.map.range B).mp hB)
    (fun f g B E hf hg => (h.relation f g B E hf hg).trans
      ⟨fun hfg => (hP f g).mpr ⟨(fnq.bound_l hf).1, (fnq.bound_l hg).1, hfg⟩,
        fun hfg => ((hP f g).mp hfg).2.2⟩)).mpr
  apply wf_of_no_desc_l hZF hDC
  intro a ha hd
  let η := ((⟨fun _ => D, fun _ => D⟩ : Env M 1).push R).push a
  let ψ : BinarySchema 3 := { body := .forallE (.iff (.mem .newest (.bound 1))
    (.conj (.mem .newest (.bound 5)) (ew_down_m (.bound 4) (.bound 3) (.bound 2) .newest))) }
  have sat n B : ψ.denote η n B ↔ ∀ v, M.mem v B ↔ M.mem v D ∧ Ew_down_d R a n v := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, ew_down_sat_l hZF.1]; rfl
  have trace n : ∃ B, ψ.denote η n B := by
    let χ : UnarySchema 3 := { body := ew_down_m (.bound 3) (.bound 2) (.bound 1) .newest }
    obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases n (Fin.cases a (fun _ => R)), fun _ => D⟩ D
    exact ⟨B, (sat n B).mpr fun v => (hB v).trans (and_congr_right fun _ => ew_down_sat_l hZF.1 _ _ _ _ _)⟩
  have member n B (hn : M.mem n ω) (hB : ψ.denote η n B) : M.mem B U := by
    obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
    obtain ⟨f, _, hnf⟩ := ha.2.1 n hn
    obtain ⟨g, _, hmg⟩ := ha.2.1 m hmω
    obtain ⟨E, hEV, he⟩ := ((hP g f).mp (hd n m f g hm hnf hmg)).2.2
    apply hU.2.2.1 E B (hVU E hEV) _ (fun v hv => ((sat n B).mp hB v |>.mp hv).1)
    intro v hv
    obtain ⟨y, _, x, _, hvy, hvx, hr⟩ := he v hv
    exact ((sat n B).mp hB v).mpr ⟨hU.1 E (hVU E hEV) v hv,
      m, f, g, x, y, hm, hnf, hmg, hvx, hvy, hr⟩
  obtain ⟨H, hH, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := ω) (target := U)
    (fun n _ => trace n) (fun n _ B E hB hE => hZF.1.eq_of_same_members B E
      fun v => ((sat n B).mp hB v).trans ((sat n E).mp hE v).symm) member
  obtain ⟨v, hvD, meet⟩ := hc H (fn0_of_function_l (ZF.modelsKP hZF) hH)
  have down n (hn : M.mem n ω) : Ew_down_d R a n v := by
    obtain ⟨B, _, hnB⟩ := hH.2.2 n hn
    exact ((sat n B).mp ((spec n B).mp hnB).2 v |>.mp (meet n B hn hnB)).2
  let δ : Env M 2 := (⟨fun _ => a, fun _ => a⟩ : Env M 1).push v
  let χ : BinarySchema 2 := { body := .existsE (.conj (rd_entry_m (.bound 2) .newest (.bound 4))
    (rd_entry_m (.bound 3) (.bound 1) .newest)) }
  have val n x : χ.denote δ n x ↔ ∃ f, Rd_entry_d n f a ∧ Rd_entry_d v x f := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨b, hb, hb'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I χ δ (source := ω) (target := X)
    (fun n hn => by
      obtain ⟨f, hfG, hnf⟩ := ha.2.1 n hn
      obtain ⟨x, _, hvx⟩ := (h.map.functions f hfG).2.1 v hvD
      exact ⟨x, (val n x).mpr ⟨f, hnf, hvx⟩⟩)
    (fun n _ x y hx hy => by
      obtain ⟨f, hnf, hvx⟩ := (val n x).mp hx
      obtain ⟨g, hng, hvy⟩ := (val n y).mp hy
      have e := (fn0_function_l (ZF.modelsKP hZF) ha).1.2 n g f hng hnf
      exact (fn0_function_l (ZF.modelsKP hZF) (h.map.functions f (ha.bound_l hnf).2)).1.2 v x y hvx (e ▸ hvy))
    (fun n x _ hx => ((val n x).mp hx).elim fun f hh => (h.map.functions f (ha.bound_l hh.1).2 |>.bound_l hh.2).2)
  apply wf_no_desc_l hZF hω hw (fn0_of_function_l (ZF.modelsKP hZF) hb)
  intro n m x y hnm hnx hmy
  obtain ⟨f, hnf, hvx⟩ := (val n x).mp ((hb' n x).mp hnx).2
  obtain ⟨g, hmg, hvy⟩ := (val m y).mp ((hb' m y).mp hmy).2
  exact (ew_down_value_l hZF.1 ha h.map.functions hnm hnf hmg hvx hvy).mp (down n (ha.bound_l hnf).1)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁强嵌入同时产生全部有限支撑测度与分量商结构

先用同一个有限次幂集容器覆盖字母表上的所有关系图，再选择覆盖它的强嵌入。
因此有限支撑与完整对局都在目标载体内；各分量的商结构允许任意秩的源载体。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem woodin_components_l (hZF : M.Models ZF) {δ} (hd : Woodin_d I δ) :
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧ M.IsOrdinal κ ∧ M.mem ω κ ∧
      ∀ L, M.mem L δ → M.MemberSubset ω L → ∃ ν N B j W k S F,
        Wd_witness_d I ω δ X A κ ν N B j W k ∧ M.mem L ν ∧ M.mem L k ∧
        Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S ∧ M.mem S N ∧ Es_family_d I j κ L S F ∧
        (∀ a U, M.PairMember I a U F → ∃ n D, Fn0_d n L a ∧ (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧
          Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U ∧ Ed_complete_d κ D U ∧
          ∀ Q R, (∃ x, M.mem x Q) → ∃ c G p C T,
            (∀ f, M.mem f G ↔ Fn0_d D Q f) ∧ Rp_model_d I D Q U R c G p C T) ∧
        Es_coherent_d I ω κ L F ∧
        ∀ H f, Ef_levels_d ω κ H → Es_fiber_d I ω L F H f →
          ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  obtain ⟨ω, X, hω, hωδ, hr, _, hV, hd⟩ := hd
  obtain ⟨D, hD⟩ := hr.2.1
  refine ⟨ω, X, hω, hV, fun A hA => ?_⟩
  obtain ⟨κ, hκ, hk⟩ := hd A hA
  obtain ⟨N₀, B₀, j₀, W₀, k₀, h₀⟩ := hk ω hωδ
  have hc₀ := h₀.2.2.2.2.2.2.1
  have hωκ := ed_critical_omega_l I hZF hω h₀.2.2.2.2.2.1 (v_transitive_l I hV) h₀.1 hc₀
  refine ⟨κ, hκ, hc₀.ordinal, hωκ, fun L hL hωL => ?_⟩
  obtain ⟨R, hRX, hR⟩ := v_relation_cover_l I hV hD.1 (ZF.v_ordinal_mem_l I hZF hV hL)
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF R
  have bound {n a} (hn : M.MemberSubset n L) (ha : Fn0_d n L a) : M.mem a R :=
    hR a fun p hp => (ha.1 p hp).elim fun i hi => hi.2.elim fun b hb => ⟨i, hn i hi.1, b, hb⟩
  obtain ⟨ν, N, B, j, W, k, hw, hLν, hLk, hQN⟩ := wd_cover_embedding_l I hZF hV hD.1 hk hL
    (v_power_mem_l I hV hD.1 hRX hQ)
  obtain ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩ := hw
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω L
  have hSN : M.mem S N := hN Q hQN S ((hQ S).mpr fun a ha => by
    obtain ⟨n, hn, hna⟩ := (hS a).mp ha
    exact bound (fun i hi => hωL i (hω.transitive (ZF.modelsKP hZF) n hn i hi)) (fn0_of_function_l (ZF.modelsKP hZF) hna))
  obtain ⟨G, hG⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) ω L
  have hGN : M.mem G N := hN Q hQN G ((hQ G).mpr fun f hf =>
    bound hωL (fn0_of_function_l (ZF.modelsKP hZF) ((hG f).mp hf)))
  obtain ⟨F, hF⟩ := es_family_exists_l I hZF hω hS j κ
  refine ⟨ν, N, B, j, W, k, S, F, ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩, hLν, hLk, hS, hSN, hF,
    ?_,
    es_coherent_l I hZF hω hV hD.1 hj hN hc (hc.ordinal_image.transitive L hLk) (hN S hSN) hF,
    fun _ _ hH hf => ef_common_fiber_l I hZF hω hV hD.1 hj hN hc
      (hc.ordinal_image.transitive L hLk) hG hGN hH ((es_fiber_iff_l I (ZF.modelsKP hZF) hS hF hH).mp hf)⟩
  intro a U ha
  obtain ⟨n, D, hn, hD, hd, hu, hc⟩ := es_family_ultra_l I hZF hω hV hD.1 hj hN hc
    (hc.ordinal_image.transitive L hLk) hS (hN S hSN) hF ha
  refine ⟨n, D, hn, hD, hd, hu, hc, fun Q R hQ => ?_⟩
  obtain ⟨B, hB⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) D Q
  obtain ⟨x, hx⟩ := hQ
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF (kp_pair_l (ZF.modelsKP hZF)) (source := D) hx
  obtain ⟨G, c, p, C, T, hG, hm⟩ := rp_family_model_l I hZF hu.1.base_l ((hB f).mpr hf)
    (fn0_of_function_l (ZF.modelsKP hZF) hf) R
  exact ⟨c, G, p, C, T, fun g => (hG g).trans ⟨And.right,
    fun hg => ⟨(hB g).mpr (fn0_function_l (ZF.modelsKP hZF) hg), hg⟩⟩, hm⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁基数产生的实际良基分量族

保留同一测度族的任意坐标协调与共同纤维性质，并自动为每个分量构造良基商。
源关系可位于任意秩；原强嵌入只用于产生测度，不作用于代表函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_wf_components_l (hM : M.Models ZFDC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFDC.models_zf_l hM))) δ) :
    let I := kp_pair_l (ZF.modelsKP (ZFDC.models_zf_l hM))
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧
      ∀ L, M.mem L δ → M.MemberSubset ω L → ∃ ν N B j W k S F,
        Wd_witness_d I ω δ X A κ ν N B j W k ∧ M.mem L k ∧
        Fseq_space_d I ω L S ∧ Es_family_d I j κ L S F ∧ Es_coherent_d I ω κ L F ∧
        (∀ H f, Ef_levels_d ω κ H → Es_fiber_d I ω L F H f → ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g) ∧
        ∀ a U, M.PairMember I a U F → ∃ n D, Fn0_d n L a ∧ (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧
          Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U ∧ Ed_complete_d κ D U ∧
          ∀ Q R, (∃ x, M.mem x Q) → Wf_rel_d Q R → ∃ c G q C T,
            (∀ f, M.mem f G ↔ Fn0_d D Q f) ∧ Rp_model_d I D Q U R c G q C T ∧ Wf_rel_d C T := by
  let hZF := ZFDC.models_zf_l hM
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, components⟩ := woodin_components_l I hZF hd
  refine ⟨ω, X, hω, hX, fun A hA => ?_⟩
  obtain ⟨κ, hκ, _, hωκ, family⟩ := components A hA
  refine ⟨κ, hκ, fun L hL hωL => ?_⟩
  obtain ⟨ν, N, B, j, W, k, S, F, hw, _, hLk, hS, _, hF, component, coherent, fiber⟩ := family L hL hωL
  refine ⟨ν, N, B, j, W, k, S, F, hw, hLk, hS, hF, coherent, fiber, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hD, hu, hU, hc, models⟩ := component a U ha
  refine ⟨n, D, hn, hD, hu, hU, hc, fun Q R hQ hR => ?_⟩
  obtain ⟨c, G, q, C, T, hG, hm⟩ := models Q R hQ
  exact ⟨c, G, q, C, T, hG, hm, rp_wf_l hZF hω (ZFDC.dc_l hM hω) hU.1
    (ed_countable_l hωκ hU.2.1 hc) (fun _ => id) hR hm⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁基数产生标准短扩展器

临界点随谓词固定，长度可取临界点与 δ 之间的任意序数。输出同一个实际
测度族和算子，并证明算子恰为原强嵌入的有限支撑限制；背景仅需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_short_l (hZF : M.Models ZF) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP hZF)) δ) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω V, M.IsOmega ω ∧ V_d I δ V ∧ ∀ A, M.MemberSubset A V → ∃ κ, M.mem κ δ ∧
      ∀ L, M.mem L δ → M.mem κ L → ∃ ν N B j W k S F K E,
        Wd_witness_d I ω δ V A κ ν N B j W k ∧ M.mem L ν ∧ M.mem L k ∧ Fseq_space_d I ω L S ∧ M.mem S N ∧
        Fseq_space_d I ω κ K ∧ Es_family_d I j κ L S F ∧ Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F ∧
        Ex_operator_d K S F E ∧ Ex_derived_d j S E := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hδ : M.IsLimitOrdinal δ := by obtain ⟨_, _, _, _, hr, _⟩ := hd; exact hr.isLimitOrdinal
  obtain ⟨ω, V, hω, hV, all⟩ := woodin_components_l I hZF hd
  refine ⟨ω, V, hω, hV, fun A hA => ?_⟩
  obtain ⟨κ, hκ, hκo, hωκ, family⟩ := all A hA
  refine ⟨κ, hκ, fun L hL hκL => ?_⟩
  have hLo := hδ.1.mem hL
  have hωL : M.MemberSubset ω L := fun x hx => hLo.transitive κ hκL x (hκo.transitive ω hωκ x hx)
  obtain ⟨ν, N, B, j, W, k, S, F, hw, hLν, hLk, hS, hSN, hF, _, _, complete⟩ := family L hL hωL
  have hj := hw.2.2.2.2.2.1
  have hc := hw.2.2.2.2.2.2.1
  have hsub := hc.ordinal_image.transitive L hLk
  have hpre := es_pre_l hZF hω hV hδ hj hw.1 hc hLo hκL hsub hS (hw.1 S hSN) hF
  have short : Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F := ⟨hpre, fun H f hH hf => (complete H f hH hf).imp fun _ hh => hh.2⟩
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨E, he⟩ := ex_operator_exists_l hZF K S F
  exact ⟨ν, N, B, j, W, k, S, F, K, E, hw, hLν, hLk, hS, hSN, hK, hF, short, he,
    ex_derived_l hZF hω hV hδ hj hw.1 hc hsub hS (hw.1 S hSN) hF hK he⟩

end YesMetaZFC.SetTheory.LargeCardinal

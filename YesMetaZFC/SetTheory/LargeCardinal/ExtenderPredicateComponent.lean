import YesMetaZFC.SetTheory.LargeCardinal.DerivedPredicate
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderElementary
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFactor
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullEmbedding
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.RelationChange

/-! # 在既有分量上扩张谓词

商类和代表投影原封保留；新关系沿规范分量映射拉回。Vδ=Hδ 的实际
小定义域闭性证明原代表族已经完整，随后可调用任意关系的 Łoś 定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_predicate_component_l {ω δ κ k K L X R A Y B j c₀ R₀ c₁ R₁ S F J O Z D p T V q c C W g W' a b : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hδ : M.IsRegularCardinal I δ) (hωδ : M.mem ω δ)
    (hV : V_d I δ X) (hH : H_d I δ X)
    (hx : Spred_d I c₀ X A R₀) (hy : Spred_d I c₁ Y B R₁) (hj : Smap_d I ω c₀ c₁ X Y j)
    (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k) (hL : M.MemberSubset L k)
    (hSY : M.MemberSubset S Y) (family : Es_family_d I j κ L S F)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (system : Ep_system_d hZF ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (model : Smdl_d I c C W) (hg : M.IsSetInjectionFromTo I g C Y)
    (rel : ∀ E H y z, Rd_entry_d E y g → Rd_entry_d H z g → (Rd_entry_d E H W' ↔ Rd_entry_d y z R₁))
    (any : ∀ u a H f E y, Rd_entry_d u E q → KPair_d M u a H → M.mem f H →
      Rd_entry_d E y g → Ee_value_d j a f y) (hab : Rd_entry_d a b Z) :
    ∃ n Q U G r H V₀ e V₁ v, M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n Q ∧ Rd_entry_d a U F ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d Q X f) ∧ Rp_model_d I Q X U R b G r H V₀ ∧
      Rp_model_d I Q X U R₀ e G r H V₁ ∧ (∀ f, Fn0_d Q X f → M.mem f G) ∧
      M.IsSetInjectionFromTo I v H C ∧
      (∀ E H x y, Rd_entry_d E x v → Rd_entry_d H y v → (Rd_entry_d E H V₁ ↔ Rd_entry_d x y W')) ∧
      ∀ E E', Rd_entry_d E E' v ↔ M.mem E H ∧ ∃ u, KPair_d M u a E ∧ Rd_entry_d u E' q := by
  have embed : Spred_emb_d I ω X A Y B j := ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩
  obtain ⟨_, _, models⟩ := system.models
  obtain ⟨n, Q, U, G, r, H, V₀, hn, ha, hQ, haU, hG, hm⟩ := models a b hab
  obtain ⟨v, hv, vs⟩ := ep_stage_embedding_l hZF source.omega system limit
    (system.toEp_graph_d.elementary_l hZFC source (hF.source_l hZF X) (coherent.source_l I X)) model hab hm.code
  obtain ⟨e, V₁, code, vr⟩ := smdl_pull_l hZF hm.code.2.1 hv.1.1 W'
  obtain ⟨haS, m, Q₀, ha₀, hQ₀, hu⟩ := (family.2.2 a U).mp haU
  have eq := ha₀.domain_eq_l hZF.1 ha
  subst m
  have eq := hZF.1.eq_of_same_members Q₀ Q (fun s => (hQ₀ s).trans (hQ s).symm)
  subst Q₀
  have hQX := source.space_mem_l hZF hn hQ
  obtain ⟨Q', _, hjQ⟩ := hj.1.1.2.2 Q hQX
  have hωκ := ed_critical_omega_l I hZF source.omega embed source.transitive hY hc
  have haQ := es_seed_l I hZF source.omega embed source.transitive hY
    (hc.fixed n (hc.ordinal.transitive ω hωκ n hn)) hc.image hjQ hQ hL (hSY a haS) ha
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF Q
  have hPX := source.transitive P (ZF.v_power_mem_l I hZF hV hδ.isLimitOrdinal hQX hP)
  have sf f (hf : M.mem f G) := source.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2
  have ultra := hF.at_l hZF.1 haU ha hQ
  have newModel : Rp_model_d I Q X U R₀ e G r H V₁ := ⟨hm.map, code, by
    intro f f' E E' hf hf'
    obtain ⟨x, _, hEx⟩ := hv.1.1.2.2 E (hm.map.projection.output_mem_of_pairMember hf)
    obtain ⟨x', _, hEx'⟩ := hv.1.1.2.2 E' (hm.map.projection.output_mem_of_pairMember hf')
    obtain ⟨y, _, hxy⟩ := hg.1.2.2 x (hv.1.1.output_mem_of_pairMember hEx)
    obtain ⟨y', _, hxy'⟩ := hg.1.2.2 x' (hv.1.1.output_mem_of_pairMember hEx')
    obtain ⟨_, u, hp, hux⟩ := (vs E x).mp hEx
    obtain ⟨_, u', hp', hux'⟩ := (vs E' x').mp hEx'
    have ey := any u a E f x y hux hp (hm.map.representative_l I ultra.1.base_l hf) hxy
    have ey' := any u' a E' f' x' y' hux' hp' (hm.map.representative_l I ultra.1.base_l hf') hxy'
    exact (vr E E' x x' hEx hEx').trans ((rel x x' y y' hxy hxy').trans
      (ed_predicate_evaluation_l hZF source.omega hx hy hj source.transitive hY hjQ haQ hP hPX hu
        (sf f (hm.map.projection.input_mem_of_pairMember hf))
        (sf f' (hm.map.projection.input_mem_of_pairMember hf')) ey ey').symm)⟩
  exact ⟨n, Q, U, G, r, H, V₀, e, V₁, v, hn, ha, hQ, haU, hG, hm, newModel,
    fun f hf => (hG f).mpr ⟨ZFC.h_function_l hZFC source.omega hδ hωδ hH hQX
      (fn0_function_l (ZF.modelsKP hZF) hf), hf⟩, hv.1, vr, vs⟩

/-- 原过渡图在扩张关系下仍对全部内部代码初等。 -/
theorem ep_predicate_map_l {ω κ K L X R F a b m n s Q₀ Q₁ U V G₀ G₁ r₀ r₁ H₀ H₁ c₀ c₁ T₀ T₁ j c S : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (hm : M.mem m ω) (hn : M.mem n ω) (hs : Fn0_d m n s) (hb : Fn0_d n L b) (ha : Cp0_d m n L s b a)
    (hQ₀ : Ep_space_d κ m Q₀) (hQ₁ : Ep_space_d κ n Q₁) (haU : Rd_entry_d a U F) (hbV : Rd_entry_d b V F)
    (hG₀ : ∀ f, M.mem f G₀ ↔ M.mem f X ∧ Fn0_d Q₀ X f) (hG₁ : ∀ f, M.mem f G₁ ↔ M.mem f X ∧ Fn0_d Q₁ X f)
    (hp : Rp_model_d I Q₀ X U S c₀ G₀ r₀ H₀ T₀) (hq : Rp_model_d I Q₁ X V S c₁ G₁ r₁ H₁ T₁)
    (full₀ : ∀ f, Fn0_d Q₀ X f → M.mem f G₀) (full₁ : ∀ f, Fn0_d Q₁ X f → M.mem f G₁)
    (code : Smdl_d I c X S) (hj : M.IsSetInjectionFromTo I j H₀ H₁)
    (spec : ∀ E H, Rd_entry_d E H j ↔ M.mem E H₀ ∧ M.mem H H₁ ∧ Ep_arrow_d ω κ L X a b E H) :
    Smap_d I ω c₀ c₁ H₀ H₁ j := by
  obtain ⟨t, K', _, ht, ts, hK, ks⟩ := source.family_l hZF hm hn hs hQ₀ hQ₁ hG₀ hG₁
  obtain ⟨P₀, hP₀⟩ := ZF.exists_powerSet hZF Q₀
  obtain ⟨P₁, hP₁⟩ := ZF.exists_powerSet hZF Q₁
  have push : Push_d Q₀ Q₁ P₀ P₁ U V t := ⟨ht, fun E hE => by
    obtain ⟨H, hH, eq⟩ := coherent m n s b a U V E hm hn hs hb ha hbV haU
      (fun r hr => (hQ₀ r).mp ((hP₀ E).mp hE r hr))
    exact ⟨H, (hP₁ H).mpr (fun v hv => (hQ₁ v).mpr ((hH v).mp hv).1), fun v => (hH v).trans
      ⟨fun ⟨hv, r, hr, hvr⟩ => ⟨(hQ₁ v).mpr hv, r, hr, (ts v r).mpr ⟨(hQ₁ v).mpr hv, hvr⟩⟩,
        fun ⟨hv, r, hr, hvr⟩ => ⟨(hQ₁ v).mp hv, r, hr, ((ts v r).mp hvr).2⟩⟩, eq⟩⟩
  have hu := hF.at_l hZF.1 haU ha.1 hQ₀
  have hv := hF.at_l hZF.1 hbV hb hQ₁
  apply rp_full_embedding_l hZFC source.omega code hP₀ hu hv push hp hq full₀ full₁ hK
    (fun f g hfg => ((ks f g).mp hfg).2.2) hj
  intro f g E H hfg hf hg
  exact (spec E H).mpr ⟨hp.map.projection.output_mem_of_pairMember hf, hq.map.projection.output_mem_of_pairMember hg,
    m, n, s, f, g, hm, hn, hs, hb, ha, hp.map.representative_l I hu.1.base_l hf,
    hq.map.representative_l I hv.1.base_l hg, ep_pull_of_comp_l hQ₀ hQ₁ ht
      (hp.map.functions f (hK.input_mem_of_pairMember hfg)) ts ((ks f g).mp hfg).2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

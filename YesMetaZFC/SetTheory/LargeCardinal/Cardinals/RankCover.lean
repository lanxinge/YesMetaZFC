import YesMetaZFC.SetTheory.CumulativeRelative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Coordinates
import YesMetaZFC.SetTheory.Card.SmallEnumeration
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.InaccessibleHierarchy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Represent

/-! # 原强嵌入的像历史在已覆盖秩层处取真实值

传输一个源中实际递归历史的全称有界证书，而非假定目标的内部幂集就是
背景幂集。原强性的秩覆盖使指定阶段的全部子集可见，逐层比较消去相对性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ed_hierarchy_l (hZF : M.Models ZF) {ω δ X A Y B j κ k U : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hκ : M.mem κ δ) (hk : Rd_entry_d κ k j) (hU : V_d (kp_pair_l (ZF.modelsKP hZF)) κ U) :
    ∃ H F U' H' F', M.mem H X ∧ M.mem F X ∧ Rd_entry_d U U' j ∧ Rd_entry_d H H' j ∧ Rd_entry_d F F' j ∧
      (∀ t, Vc_d κ U H F t) ∧ (∀ α V, Rd_entry_d α V F → V_d (kp_pair_l (ZF.modelsKP hZF)) α V) ∧
      (∀ t, M.mem t Y → Vc_d k U' H' F' t) ∧
      ∀ ν V, M.mem ν k → V_d (kp_pair_l (ZF.modelsKP hZF)) ν V → M.MemberSubset V Y → Rd_entry_d ν V F' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨H, F, hHX, hFX, cert, history⟩ := vr_source_l hZF hX hδ hκ hU
  obtain ⟨U', hUY, hjU⟩ := hj.2.2 U (ZF.v_mem_l I hZF hU hX hκ)
  obtain ⟨H', hHY, hjH⟩ := hj.2.2 H hHX
  obtain ⟨F', _, hjF⟩ := hj.2.2 F hFX
  let φ : Formula 1 5 := vc_matrix_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := spred_forall_delta_l I hZF hω h ht hY φ (by simp -implicitDefEqProofs [φ]) (vc_matrix_delta_l ..)
    ⟨Fin.cases F (Fin.cases H (Fin.cases U (fun _ => κ))), fun _ => κ⟩
    ⟨Fin.cases F' (Fin.cases H' (Fin.cases U' (fun _ => k))), fun _ => k⟩
    (Fin.cases hjF (Fin.cases hjH (Fin.cases hjU (fun _ => hk))))
  simp only [φ, vc_matrix_sat_l (ZF.modelsKP hZF)] at tr
  have target := tr.mp (fun t _ => cert t)
  have fn := (target U' hUY).2.1
  have ko := (target U' hUY).1
  refine ⟨H, F, U', H', F', hHX, hFX, hjU, hjH, hjF, cert, history, target, fun ν V hν hV cover => ?_⟩
  obtain ⟨W, hW, hνW⟩ := fn.2.1 ν hν
  have eq := vr_compare_l hZF hY (hY H' hHY) fn (ko.transitive ν hν) (hY H' hHY W hW) hV cover
    (fun β hβ T hβT t ht => (target t ht).2.2.1 β (ko.transitive ν hν β hβ) T (fn.bound_l hβT).2 hβT)
    (fun t ht => (target t ht).2.2.1 ν hν W hW hνW)
  exact eq ▸ hνW

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 秩层最小枚举的有界读取

枚举包存实际序数域和满射图。最小性只比较临界点以下的候选域，候选满射
作为一个自由实参，故整条阶段检验仍为 Δ₀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Su0_d (D X f : M.Domain) : Prop := Fn0_d D X f ∧ ∀ x, M.mem x X → ∃ a, M.mem a D ∧ Rd_entry_d a x f
def su0_m {d} (D X f : Term d) : Formula 1 d := .conj (fn0_m D X f)
  (Formula.forallMem X (Formula.existsMem D.weaken (rd_entry0_m .newest (.bound 1) f.weaken.weaken)))
derive_free_closed su0_m
theorem su0_delta_l {d} (D X f : Term d) : (su0_m D X f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
theorem su0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D X f : Term d) :
    Formula.satisfies ρ (su0_m D X f) ↔ Su0_d (D.eval ρ) (X.eval ρ) (f.eval ρ) := by
  simp only [su0_m, Su0_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Er_enum_d (I : kpair_convention_l.Interpretation M) (α p : M.Domain) : Prop :=
  ∃ V μ g, V_d I α V ∧ KPair_d M p μ g ∧ M.IsCardinal I μ ∧ M.IsSetBijectionFromTo I g μ V
def er_enum_m {d} (α p : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (v_m kpair_convention_l α.weaken.weaken.weaken (.bound 2))
    (.conj (kpair_m p.weaken.weaken.weaken (.bound 1) .newest) (.conj
      (Formula.isCardinal kpair_convention_l (.bound 1))
      (Formula.isBijectionFromTo kpair_convention_l .newest (.bound 1) (.bound 2)))))))
derive_free_closed er_enum_m
theorem er_enum_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (α p : Term d) : Formula.satisfies ρ (er_enum_m α p) ↔ Er_enum_d I (α.eval ρ) (p.eval ρ) := by
  simp only [er_enum_m, Er_enum_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, v_sat_l I hE,
    kpair_sat_l M hE, Formula.satisfies_isCardinal_iff I hE, Formula.satisfies_isBijectionFromTo_iff I hE,
    Definitional.Term.eval_weaken]; rfl

def Er_stage_d (κ H F T G h : M.Domain) : Prop := ∀ α, M.mem α κ → ∀ U, M.mem U H → ∀ p, M.mem p T →
  Rd_entry_d α U F → Rd_entry_d α p G → ∃ μ, M.mem μ T ∧ ∃ g, M.mem g T ∧ KPair_d M p μ g ∧
    Su0_d μ U g ∧ ∀ ν, M.mem ν κ → Su0_d ν U h → M.MemberSubset μ ν
def er_stage_m {d} (κ H F T G h : Term d) : Formula 1 d :=
  Formula.forallMem κ (Formula.forallMem H.weaken (Formula.forallMem T.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 2) .newest G.weaken.weaken.weaken)
        (Formula.existsMem T.weaken.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken.weaken
          (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.conj (su0_m (.bound 1) (.bound 3) .newest)
            (Formula.forallMem κ.weaken.weaken.weaken.weaken.weaken
              (.imp (su0_m .newest (.bound 4) h.weaken.weaken.weaken.weaken.weaken.weaken)
                (Formula.subset (.bound 2) .newest)))))))))))
derive_free_closed er_stage_m
theorem er_stage_delta_l {d} (κ H F T G h : Term d) : (er_stage_m κ H F T G h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..)
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.conj (su0_delta_l ..)
      (.forallMem _ (.imp (su0_delta_l ..) (.atom _ _ _)))))))))))
theorem er_stage_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ H F T G h : Term d) :
    Formula.satisfies ρ (er_stage_m κ H F T G h) ↔
      Er_stage_d (κ.eval ρ) (H.eval ρ) (F.eval ρ) (T.eval ρ) (G.eval ρ) (h.eval ρ) := by
  simp only [er_stage_m, Er_stage_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, kpair0_sat_l hE,
    su0_sat_l hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源中的实际秩层枚举族

先对每个 Vα 取最小序数枚举，再用原对象选择公理统一成图。正则 Hδ 的
小定义域函数封闭保证整张枚举图属于 Vδ，随后提供可传输的有界最小性检验。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem er_family_l (hZFC : M.Models ZFC) {ω δ X κ : M.Domain} (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hκ : M.mem κ δ) :
    ∃ G T, M.mem G X ∧ M.mem T X ∧ M.TransitiveSet T ∧ M.mem κ T ∧ M.mem G T ∧ Fn0_d κ T G ∧
      ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) α p := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hH := ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hX
  have hκX := ZF.v_ordinal_mem_l I hZF hX hκ
  have ht := v_transitive_l I hX
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => κ⟩
  let φ : BinarySchema 0 := { body := er_enum_m (.bound 1) .newest }
  have sat α p : φ.denote ρ α p ↔ Er_enum_d I α p := er_enum_sat_l I hZF.1 ..
  obtain ⟨G, hg, gs⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := κ) (Y := X) (fun α hα => by
    have hαδ := hr.isCardinal.1.transitive κ hκ α hα
    obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF (hr.isCardinal.1.mem hαδ)
    obtain ⟨ξ, hξ, hVξ⟩ := ZFC.inaccessible_level_small_l I hZFC hω hωδ hr hs hαδ hV
    obtain ⟨μ, g, hμδ, hμ, bij⟩ := ZF.small_enumeration_l I hZF hr.isCardinal hξ hVξ
    have hμX := ZF.v_ordinal_mem_l I hZF hX hμδ
    have hVX := ZF.v_mem_l I hZF hV hX hαδ
    have hgX := ZFC.h_function_l hZFC hω hr hωδ hH hμX (bij.1.1.mono_target_l I (ht V hVX))
    obtain ⟨p, hp⟩ := I.total μ g
    exact ⟨p, ZFC.h_kpair_l hZFC hω hr hωδ hH hp hμX hgX, (sat α p).mpr ⟨V, μ, g, hV, hp, hμ, bij⟩⟩)
  have hGX := ZFC.h_function_l hZFC hω hr hωδ hH hκX hg
  obtain ⟨p, hp⟩ := I.total κ G
  have hpX := ZFC.h_kpair_l hZFC hω hr hωδ hH hp hκX hGX
  obtain ⟨β, T, hβ, hT, hpT⟩ := (ZF.v_limit_mem_l I hZF hX hr.isLimitOrdinal.2.2 p).mp hpX
  have hTt := v_transitive_l I hT
  obtain ⟨hκT, hGT⟩ := hp.mem_l M hTt hpT
  have bound α p (hap : Rd_entry_d α p G) : M.mem p T := by
    obtain ⟨r, hr, hrG⟩ := hap
    exact (hr.mem_l M hTt (hTt G hGT r hrG)).2
  exact ⟨G, T, hGX, ZF.v_mem_l I hZF hT hX hβ, hTt, hκT, hGT,
    (fn0_of_function_l (ZF.modelsKP hZF) hg).retarget_l bound, fun α p hp => (sat α p).mp (gs α p hp)⟩

theorem er_stage_l (hZF : M.Models ZF) {κ H F T G : M.Domain} (hκ : M.IsOrdinal κ) (hT : M.TransitiveSet T)
    (history : ∀ α U, Rd_entry_d α U F → V_d (kp_pair_l (ZF.modelsKP hZF)) α U)
    (enums : ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l (ZF.modelsKP hZF)) α p) (h : M.Domain) :
    Er_stage_d κ H F T G h := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro α _ U _ p hp hαU hαp
  obtain ⟨V, μ, g, hV, hpg, hμ, hg⟩ := enums α p hαp
  have eq := ZF.v_unique_l I hZF hV (history α U hαU)
  subst V
  obtain ⟨hμT, hgT⟩ := hpg.mem_l M hT hp
  exact ⟨μ, hμT, g, hgT, hpg, ⟨fn0_of_function_l (ZF.modelsKP hZF) hg.1.1, hg.2⟩,
    fun ν hν hsur => ZF.enumeration_minimal_l I hZF hμ hg (hκ.mem hν)
      (fn0_function_l (ZF.modelsKP hZF) hsur.1) hsur.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 为指定秩层实际选择足够长的短扩展器长度

长度同时高于临界点、秩指标和一个最小枚举的序数域，并在 V_L 中包含
整张枚举图。原构造的强度高于 L，故这些数据都进入原目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem er_length_l (hZFC : M.Models ZFC) {ω δ X κ ν : M.Domain} (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hκ : M.mem κ δ) (hν : M.mem ν δ) :
    ∃ L V μ g U, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ M.mem μ L ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ν V ∧
      V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L U ∧ M.mem g U ∧ Su0_d μ V g := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hδ := hr.isLimitOrdinal
  have ht := v_transitive_l I hX
  have hH := ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hX
  obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF (hr.isCardinal.1.mem hν)
  obtain ⟨ξ, hξ, hVξ⟩ := ZFC.inaccessible_level_small_l I hZFC hω hωδ hr hs hν hV
  obtain ⟨μ, g, hμ, _, hg⟩ := ZF.small_enumeration_l I hZF hr.isCardinal hξ hVξ
  have hμX := ZF.v_ordinal_mem_l I hZF hX hμ
  have hVX := ZF.v_mem_l I hZF hV hX hν
  have hgX := ZFC.h_function_l hZFC hω hr hωδ hH hμX (hg.1.1.mono_target_l I (ht V hVX))
  obtain ⟨α, W, hα, hW, hgW⟩ := (ZF.v_limit_mem_l I hZF hX hδ.2.2 g).mp hgX
  have above a b (ha : M.mem a δ) (hb : M.mem b δ) : ∃ c, M.mem c δ ∧ M.mem a c ∧ M.mem b c := by
    rcases hδ.1.wellOrder.linear.compare a ha b hb with same | hab | hba
    · obtain ⟨c, hc, hbc⟩ := hδ.2.2 b hb
      exact ⟨c, hc, (hZF.1.eq_of_same_members a b same).symm ▸ hbc, hbc⟩
    · obtain ⟨c, hc, hbc⟩ := hδ.2.2 b hb
      exact ⟨c, hc, (hδ.1.mem hc).transitive b hbc a hab, hbc⟩
    · obtain ⟨c, hc, hac⟩ := hδ.2.2 a ha
      exact ⟨c, hc, hac, (hδ.1.mem hc).transitive a hac b hba⟩
  obtain ⟨a, ha, hκa, hνa⟩ := above κ ν hκ hν
  obtain ⟨b, hb, hμb, hαb⟩ := above μ α hμ hα
  obtain ⟨L, hL, haL, hbL⟩ := above a b ha hb
  have hLo := hδ.1.mem hL
  obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF hLo
  exact ⟨L, V, μ, g, U, hL, hLo.transitive a haL κ hκa, hLo.transitive a haL ν hνa,
    hLo.transitive b hbL μ hμb, hV, hU,
    ZF.v_mono_l I hZF hW hU (hLo.transitive α (hLo.transitive b hbL α hαb)) g hgW,
    fn0_of_function_l (ZF.modelsKP hZF) hg.1.1, hg.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 用两个有限坐标读取秩层枚举包 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Er_hit_d (T G i r s x : M.Domain) : Prop := ∃ α, M.mem α T ∧ ∃ β, M.mem β T ∧
  ∃ p, M.mem p T ∧ ∃ μ, M.mem μ T ∧ ∃ g, M.mem g T ∧ Rd_entry_d i α s ∧ Rd_entry_d r β s ∧
    Rd_entry_d α p G ∧ KPair_d M p μ g ∧ Rd_entry_d β x g
def er_hit_m {d} (T G i r s x : Term d) : Formula 1 d :=
  let w (t : Term d) : Term (d+5) := t.weaken.weaken.weaken.weaken.weaken
  Formula.existsMem T (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
    (Formula.existsMem T.weaken.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken.weaken
      (.conj (rd_entry0_m (w i) (.bound 4) (w s)) (.conj (rd_entry0_m (w r) (.bound 3) (w s))
        (.conj (rd_entry0_m (.bound 4) (.bound 2) (w G))
          (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (rd_entry0_m (.bound 3) (w x) .newest)))))))))
derive_free_closed er_hit_m
theorem er_hit_delta_l {d} (T G i r s x : Term d) : (er_hit_m T G i r s x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..)))))))))
theorem er_hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T G i r s x : Term d) :
    Formula.satisfies ρ (er_hit_m T G i r s x) ↔
      Er_hit_d (T.eval ρ) (G.eval ρ) (i.eval ρ) (r.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [er_hit_m, Er_hit_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Er_hit_d.bound_l {T G i r s x : M.Domain} (hT : M.TransitiveSet T) (h : Er_hit_d T G i r s x) : M.mem x T := by
  obtain ⟨_, _, _, _, _, _, _, _, g, hg, _, _, _, _, p, hp, hpg⟩ := h
  exact (hp.mem_l M hT (hT g hg p hpg)).2

theorem er_hit_unique_l (hKP : M.Models KP) {T G i r s x y n κ : M.Domain}
    (hs : Fn0_d n κ s) (hG : Fn0_d κ T G)
    (enums : ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l hKP) α p)
    (hx : Er_hit_d T G i r s x) (hy : Er_hit_d T G i r s y) : x = y := by
  obtain ⟨α, _, β, _, p, _, μ, _, g, _, hi, hr, hαp, hp, hgx⟩ := hx
  obtain ⟨α', _, β', _, p', _, μ', _, g', _, hi', hr', hαp', hp', hgy⟩ := hy
  have eq := (fn0_function_l hKP hs).1.2 i α' α hi' hi
  subst α'
  have eq := (fn0_function_l hKP hs).1.2 r β' β hr' hr
  subst β'
  have eq := (fn0_function_l hKP hG).1.2 α p' p hαp' hαp
  subst p'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
  obtain ⟨V, ν, f, _, hp'', _, bij⟩ := enums α p hαp
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp''
  exact bij.1.1.1.2 β x y hgx hgy

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源内实际的双坐标枚举读取函数

有效索引读枚举值，其余输入取 κ。源内有界统一化给出总图；以下保留有效
索引的精确求值律，供原嵌入直接传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem er_lookup_l (hZF : M.Models ZF) {ω κ K X R T G n D i r : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hT : M.TransitiveSet T)
    (hTX : M.mem T X) (hGX : M.mem G X) (hκT : M.mem κ T) (hG : Fn0_d κ T G)
    (enums : ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l (ZF.modelsKP hZF)) α p)
    (hn : M.mem n ω) (hD : Ep_space_d κ n D) (hi : M.mem i n) (hr : M.mem r n) :
    ∃ f, M.mem f X ∧ Fn0_d D T f ∧
      ∀ s x, M.mem s D → Er_hit_d T G i r s x → Rd_entry_d s x f := by
  let ρ := ((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push G).push i).push r).push κ
  let φ : BinarySchema 5 := {
    body := .disj (er_hit_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (.conj (Formula.extensionalEq .newest (.bound 2)) (.neg (Formula.existsMem (.bound 6)
        (er_hit_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have sat s x : φ.denote ρ s x ↔ Er_hit_d T G i r s x ∨ (x = κ ∧ ¬ ∃ y, M.mem y T ∧ Er_hit_d T G i r s y) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, er_hit_sat_l hZF.1,
      Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_existsMem_iff]; rfl
  have hinX a (ha : M.mem a n) := source.transitive ω source.omega_mem a (source.omega.transitive (ZF.modelsKP hZF) n hn a ha)
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨f, hfX, hf, fs⟩ := sc_uniform_source_l hZF source.omega source.transitive hm source.theory φ
    (.disj (er_hit_delta_l ..) (.conj (.atom _ _ _) (.neg (.existsMem _ (er_hit_delta_l ..))))) ρ
    (Fin.cases source.cardinal_mem (Fin.cases (hinX r hr) (Fin.cases (hinX i hi) (Fin.cases hGX (fun _ => hTX)))))
    (source.space_mem_l hZF hn hD) hTX (fun s _ => by
      classical
      by_cases hit : ∃ x, M.mem x T ∧ Er_hit_d T G i r s x
      · obtain ⟨x, hx, hit⟩ := hit
        exact ⟨x, hx, (sat s x).mpr (Or.inl hit)⟩
      · exact ⟨κ, hκT, (sat s κ).mpr (Or.inr ⟨rfl, hit⟩)⟩)
  refine ⟨f, hfX, hf, fun s x hs hit => ?_⟩
  obtain ⟨y, _, hsy⟩ := hf.2.1 s hs
  rcases (sat s y).mp (fs s y hsy) with hy | ⟨_, impossible⟩
  · exact er_hit_unique_l (ZF.modelsKP hZF) ((hD s).mp hs) hG enums hy hit ▸ hsy
  · exact (impossible ⟨x, hit.bound_l hT, hit⟩).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 足够长的派生扩展器覆盖原强嵌入的指定秩层

目标中的一个短枚举界定最小像枚举的域。每个秩层对象于是成为源中同一个
双坐标函数的种子求值，再进入既有全系统的真实极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem er_cover_l (hZFC : M.Models ZFC)
    {ω δ X A Y B j κ k K R L S F J O Z D p T V q C W ν Vν μ₀ g₀ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) (hκ : M.mem κ δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X j κ k)
    (hL : M.MemberSubset L k) (hLo : M.IsOrdinal L)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) j κ L S F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (hνL : M.mem ν L) (hVν : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ν Vν)
    (hVY : M.MemberSubset Vν Y) (hμL : M.mem μ₀ L) (hgY : M.mem g₀ Y) (hg : Su0_d μ₀ Vν g₀) :
    ∀ x, M.mem x Vν → ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u x := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  have hωκ := ed_critical_omega_l I hZF source.omega h source.transitive hY hc
  have hωδ := hr.isCardinal.1.transitive κ hκ ω hωκ
  obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF hc.ordinal
  obtain ⟨H, F₀, U', H', F₁, _, _, hjU, hjH, hjF, _, history, target, levels⟩ :=
    ed_hierarchy_l hZF source.omega hX hr.isLimitOrdinal h hY hκ hc.image hU
  obtain ⟨G, Q, hGX, hQX, hQ, hκQ, _, hG, enums⟩ := er_family_l hZFC source.omega hωδ hr hs hX hκ
  obtain ⟨Q', hQY, hjQ⟩ := hj.2.2 Q hQX
  obtain ⟨G', _, hjG⟩ := hj.2.2 G hGX
  have hG' := (spred_function_l I hZF source.omega h source.transitive hY hc.image hjQ hjG).mp hG
  have hQ' : M.TransitiveSet Q' := by
    have tr := spred_delta_l I hZF source.omega h source.transitive hY (n := 1) (Formula.isTransitive (.bound 0))
      (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _) ⟨fun _ => Q, fun _ => Q⟩ ⟨fun _ => Q', fun _ => Q'⟩ (fun _ => hjQ)
    simp only [Formula.satisfies_isTransitive_iff] at tr
    exact tr.mp hQ
  have hkQ := (ed_member_l I hZF source.omega h source.transitive hY hc.image hjQ).mp hκQ
  have hνk := hL ν hνL
  have hνF := levels ν Vν hνk hVν hVY
  have hU'Y := hj.output_mem_of_pairMember hjU
  have hVνH := ((target U' hU'Y).2.1.bound_l hνF).2
  obtain ⟨p₀, hpQ, hνG⟩ := hG'.2.1 ν hνk
  let φ : Formula 1 6 := er_stage_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := spred_forall_delta_l I hZF source.omega h source.transitive hY φ
    (by simp -implicitDefEqProofs [φ]) (er_stage_delta_l ..)
    ⟨Fin.cases G (Fin.cases Q (Fin.cases F₀ (Fin.cases H (fun _ => κ)))), fun _ => κ⟩
    ⟨Fin.cases G' (Fin.cases Q' (Fin.cases F₁ (Fin.cases H' (fun _ => k)))), fun _ => k⟩
    (Fin.cases hjG (Fin.cases hjQ (Fin.cases hjF (Fin.cases hjH (fun _ => hc.image)))))
  simp only [φ, er_stage_sat_l hZF.1] at tr
  have stage := tr.mp (fun g _ => er_stage_l hZF hc.ordinal hQ history enums g) g₀ hgY
  obtain ⟨μ, hμQ, g, hggQ, hp, onto, least⟩ := stage ν hνk Vν hVνH p₀ hpQ hνF hνG
  have small := least μ₀ (hL μ₀ hμL) hg
  obtain ⟨zero, hzero, hzω⟩ := source.omega.1.1
  obtain ⟨one, h1, h1ω⟩ := source.omega.1.2 zero hzω
  obtain ⟨two, h2, h2ω⟩ := source.omega.1.2 one h1ω
  have hz2 := (h2 zero).mpr (Or.inl h1.predecessor_mem)
  have h12 := h2.predecessor_mem
  have ne : zero ≠ one := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) one (eq ▸ h1.predecessor_mem)
  obtain ⟨D₀, hD₀X, hD₀⟩ := source.space_l hZF h2ω
  obtain ⟨f, hfX, hf, read⟩ := er_lookup_l hZF source hQ hQX hGX hκQ hG enums h2ω hD₀ hz2 h12
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  obtain ⟨D₁, _, hjD⟩ := hj.2.2 D₀ hD₀X
  let ψ : Formula 1 6 := Formula.forallMem (.bound 5) (Formula.forallMem (.bound 5)
    (.imp (er_hit_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (rd_entry0_m (.bound 1) .newest (.bound 2))))
  have transfer := spred_delta_l I hZF source.omega h source.transitive hY ψ
    (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.imp (er_hit_delta_l ..) (rd_entry0_delta_l ..))))
    ⟨Fin.cases f (Fin.cases one (Fin.cases zero (Fin.cases G (Fin.cases Q (fun _ => D₀))))), fun _ => D₀⟩
    ⟨Fin.cases f' (Fin.cases one (Fin.cases zero (Fin.cases G' (Fin.cases Q' (fun _ => D₁))))), fun _ => D₁⟩
    (Fin.cases hjf (Fin.cases (hc.fixed one (hc.ordinal.transitive ω hωκ one h1ω))
      (Fin.cases (hc.fixed zero (hc.ordinal.transitive ω hωκ zero hzω)) (Fin.cases hjG (Fin.cases hjQ (fun _ => hjD))))))
  simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, er_hit_sat_l hZF.1, rd_entry0_sat_l hZF.1] at transfer
  have eval := transfer.mp (fun s hs x _ hx => read s x hs hx)
  intro x hx
  obtain ⟨β, hβ, hβx⟩ := onto.2 x hx
  have hβL := hLo.transitive μ₀ hμL β (small β hβ)
  obtain ⟨a₀, ha₀, as⟩ := ZF.exists_constantFunction hZF I (source := two) hνL
  obtain ⟨a, update, ha⟩ := senv_update_exists_l I hZF ha₀ h12 hβL
  have az := (update.2 zero ν).mpr (Or.inr ⟨ne, (as zero ν).mpr ⟨hz2, rfl⟩⟩)
  have a1 := (update.2 one β).mpr (Or.inl ⟨rfl, rfl⟩)
  have hit : Er_hit_d Q' G' zero one a x := ⟨ν, hQ' k hkQ ν hνk, β, hQ' μ hμQ β hβ,
    p₀, hpQ, μ, hμQ, g, hggQ, az, a1, hνG, hp, hβx⟩
  have haD := es_seed_l I hZF source.omega h source.transitive hY
    (hc.fixed two (hc.ordinal.transitive ω hωκ two h2ω)) hc.image hjD hD₀ hL
    (hSY a ((hS a).mpr ⟨two, h2ω, ha⟩)) (fn0_of_function_l (ZF.modelsKP hZF) ha)
  exact ee_represent_l hZF source hX hr.isLimitOrdinal h hY hc hL hS hSY hF system limit
    h2ω hD₀ (fn0_of_function_l (ZF.modelsKP hZF) ha) hfX (hf.mono_target_l (source.transitive Q hQX))
    ⟨f', hjf, eval a haD x (hit.bound_l hQ') hit⟩

/-- 不可达支撑的每个严格秩层都有短枚举，故同一系统覆盖整个 V_L。 -/
theorem er_inaccessible_cover_l (hZFC : M.Models ZFC)
    {ω δ X A Y B j κ k K R L S F J O Z D p T V q C W U : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) (hκ : M.mem κ δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X j κ k)
    (hL : M.MemberSubset L k) (hκL : M.mem κ L) (hωL : M.mem ω L)
    (rL : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (sL : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) j κ L S F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (hU : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) L U) (hUY : M.MemberSubset U Y) :
    ∀ x, M.mem x U → ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u x := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro x hx
  obtain ⟨ν, Vν, hν, hv, hxν⟩ := (ZF.v_limit_mem_l I hZF hU rL.isLimitOrdinal.2.2 x).mp hx
  obtain ⟨ℓ, V₀, μ, g, U₀, hℓ, _, _, hμ, hv₀, hu₀, hg, onto⟩ := er_length_l hZFC source.omega hωL rL sL hU hκL hν
  have vl := ZF.v_mono_l I hZF hv₀ hU (rL.isCardinal.1.transitive ν hν)
  have ul := ZF.v_mono_l I hZF hu₀ hU (rL.isCardinal.1.transitive ℓ hℓ)
  exact er_cover_l hZFC source hX hr hs hκ h hY hc hL rL.isCardinal.1
    hS hSY hF system limit hν hv₀ (fun y hy => hUY y (vl y hy)) (rL.isCardinal.1.transitive ℓ hℓ μ hμ)
    (hUY g (ul g hg)) onto x (ZF.v_unique_l I hZF hv hv₀ ▸ hxν)

end YesMetaZFC.SetTheory.LargeCardinal

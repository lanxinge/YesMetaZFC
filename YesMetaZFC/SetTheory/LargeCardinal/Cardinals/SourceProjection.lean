import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.DerivedPredicate
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinInitial
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.Model.SetTheory.Source.Field
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.Model.SetTheory.ReducedPower.ProjectionLaws

/-! # 临界点派生测度的非主性

若 κ=crit(j)，以 κ 为种子得到的超滤不包含任何单点集：
j 固定每个 x<κ，故 j({x})={x}，但种子 κ 不等于 x。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ed_nonprincipal_d (U : M.Domain) : Prop :=
  ∀ x s, (∀ y, M.mem y s ↔ y = x) → ¬ M.mem s U

def ed_nonprincipal_m {d} (U : Term d) : Formula 1 d := .forallE (.forallE (.imp
  (.forallE (.iff (.mem .newest (.bound 1)) (Formula.extensionalEq .newest (.bound 2))))
  (.neg (.mem .newest U.weaken.weaken))))
derive_free_closed ed_nonprincipal_m

theorem ed_nonprincipal_sat_l (hE : Extensional M) {d} (ρ : Env M d) (U : Term d) :
    Formula.satisfies ρ (ed_nonprincipal_m U) ↔ Ed_nonprincipal_d (U.eval ρ) := by
  simp only [ed_nonprincipal_m, Ed_nonprincipal_d, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
  rfl

theorem ed_critical_nonprincipal_l (hZF : M.Models ZF) {ω X A Y B j κ k U}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d I X j κ k) (hU : Ed_filter_d I j κ κ U) : Ed_nonprincipal_d U := by
  intro x s hs hsU
  obtain ⟨hsub, s', hjs, hκ⟩ := (hU s).mp hsU
  have hx := hsub x ((hs x).mpr rfl)
  have hjx := hc.fixed x hx
  have tr := spred_delta_l I hZF hω h hX hY (n := 2)
    (Formula.forallMem (.bound 1) (Formula.extensionalEq .newest (.bound 1)))
    (by simp) (.forallMem _ (.atom _ _ _))
    ⟨Fin.cases x (fun _ => s), fun _ => x⟩ ⟨Fin.cases x (fun _ => s'), fun _ => x⟩
    (Fin.cases hjx (fun _ => hjs))
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] at tr
  have he : κ = x := tr.mp (fun y hy => (hs y).mp hy) κ hκ
  exact KP.mem_irrefl_d (ZF.modelsKP hZF) κ (he.symm ▸ hx)

/-- 从临界点嵌入同时返回派生图、极大适当性与非主性。 -/
theorem ed_critical_measure_l (hZF : M.Models ZF) {ω X A Y B j κ k P}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d I X j κ k) (hκ : M.mem κ k) (hP : M.IsPowerSetOf P κ) (hPX : M.mem P X) :
    ∃ U, Ed_filter_d I j κ κ U ∧ FilterZF.Maximal_d (ℳ := M) κ U ∧ Ed_nonprincipal_d U := by
  obtain ⟨U, hU, hu⟩ := ed_ultrafilter_l I hZF hω h hX hY hP hPX hc.image hκ
  exact ⟨U, hU, hu, ed_critical_nonprincipal_l I hZF hω h hX hY hc hU⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 临界点严格超过内部 ω

自然数用已有 Δ₀ 谓词 N0 刻画。空集与后继保持排除有限临界点，
“全部成员为自然数”的保持及低于临界点的逐点固定排除 κ=ω。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_critical_omega_l (hZF : M.Models ZF) {ω X A Y B j κ k}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k) : M.mem ω κ := by
  obtain ⟨v, hv, hn⟩ := KPi.exists_omega_l (ZF.models_kpi_l hZF)
  have he : v = ω := hZF.1.eq_of_same_members v ω (fun n => ⟨hv.2 ω hω.1 n, hω.2 v hv.1 n⟩)
  have hnat x : M.mem x ω ↔ KP.N0_d x := he ▸ hn x
  have hjκ := hc.image
  have hne := hc.moved
  have fixed := hc.fixed
  have hfin : ¬ M.mem κ ω := by
    intro hκ
    rcases ((hnat κ).mp hκ).2.1 with he | ⟨n, hnκ, hs⟩
    · have hk := (ed_empty_l I hZF hω h hX hY hjκ).mp he
      exact hne (hZF.1.eq_of_same_members κ k (fun x => iff_of_false (he x) (hk x)))
    · have tr := spred_delta_l I hZF hω h hX hY (n := 2) (KP.succ0_m (.bound 1) (.bound 0))
        (KP.succ0_m_freeClosed _ _ rfl rfl) (KP.succ0_delta_l ..)
        ⟨Fin.cases n (fun _ => κ), fun _ => n⟩ ⟨Fin.cases n (fun _ => k), fun _ => n⟩
        (Fin.cases (fixed n hnκ) (fun _ => hjκ))
      simp only [KP.succ0_sat_l hZF.1] at tr
      have hk : M.SuccessorOf k n := tr.mp hs
      exact hne (Structure.SuccessorOf.eq hZF.1 hs hk)
  have hωne : κ ≠ ω := by
    intro he
    have tr := spred_delta_l I hZF hω h hX hY (n := 1)
      (Formula.forallMem (.bound 0) (KP.n0_m .newest))
      (by simp -implicitDefEqProofs) (.forallMem _ (KP.n0_delta_l _))
      ⟨fun _ => κ, fun _ => κ⟩ ⟨fun _ => k, fun _ => k⟩ (fun _ => hjκ)
    simp only [Formula.satisfies_forallMem_iff, KP.n0_sat_l hZF.1] at tr
    have hk : ∀ x, M.mem x k → KP.N0_d x := tr.mp (fun x hx => (hnat x).mp (he ▸ hx))
    exact hne (hZF.1.eq_of_same_members κ k (fun x =>
      ⟨fun hx => (ed_member_l I hZF hω h hX hY (fixed x hx) hjκ).mp hx,
        fun hx => he.symm ▸ (hnat x).mpr (hk x hx)⟩))
  rcases Structure.IsOrdinal.trichotomy hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) hc.ordinal
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with he | he | he
  · exact (hωne (hZF.1.eq_of_same_members ω κ he).symm).elim
  · exact he
  · exact (hfin he).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意派生测度的短交封闭

内部长度 μ<κ 的全体索引都被 j 固定。将原交集的有界定义送过 j，
每个像纤维都包含同一个种子，于是交集自身属于派生超滤；载体可以是任意实际集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ed_all_d (μ U F x : M.Domain) : Prop := ∀ i, M.mem i μ → ∀ s, M.mem s U →
  Rd_entry_d i s F → M.mem x s

def ed_all_m {d} (μ U F x : Term d) : Formula 1 d := Formula.forallMem μ
  (Formula.forallMem U.weaken (.imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
    (.mem x.weaken.weaken .newest)))
derive_free_closed ed_all_m

theorem ed_all_delta_l {d} (μ U F x : Term d) : (ed_all_m μ U F x).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.mem _ _)))

theorem ed_all_sat_l (hE : Extensional M) {d} (ρ : Env M d) (μ U F x : Term d) :
    Formula.satisfies ρ (ed_all_m μ U F x) ↔ Ed_all_d (μ.eval ρ) (U.eval ρ) (F.eval ρ) (x.eval ρ) := by
  simp only [ed_all_m, Ed_all_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Ed_complete_d (κ D U : M.Domain) : Prop := ∀ μ, M.mem μ κ → ∀ F, Fn0_d μ U F →
  ∃ r, M.mem r U ∧ ∀ x, M.mem x r ↔ M.mem x D ∧ Ed_all_d μ U F x

def ed_complete_m {d} (κ D U : Term d) : Formula 1 d := Formula.forallMem κ (.forallE (.imp
  (fn0_m (.bound 1) U.weaken.weaken .newest) (.existsE (.conj (.mem .newest U.weaken.weaken.weaken)
    (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest D.weaken.weaken.weaken.weaken)
      (ed_all_m (.bound 3) U.weaken.weaken.weaken.weaken (.bound 2) .newest))))))))
derive_free_closed ed_complete_m

theorem ed_complete_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ D U : Term d) :
    Formula.satisfies ρ (ed_complete_m κ D U) ↔ Ed_complete_d (κ.eval ρ) (D.eval ρ) (U.eval ρ) := by
  simp only [ed_complete_m, Ed_complete_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, fn0_sat_l hE, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, ed_all_sat_l hE, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF) {ω X A Y B j : M.Domain} (hω : M.IsOmega ω)
  (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
include hZF hω h hX hY

omit hX in
/-- 极限秩层中的派生超滤，对全部内部 μ<κ 长族封闭。 -/
theorem ed_complete_l {δ κ k D D' a U} (hV : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (hc : Wd_crit_d I X j κ k) (hjD : M.PairMember I D D' j) (ha : M.mem a D')
    (hU : Ed_filter_d I j a D U) : Ed_complete_d κ D U := by
  have hX := v_transitive_l I hV
  have hj : M.IsSetFunctionFromTo I j X Y := by
    obtain ⟨_, _, _, _, _, _, hj⟩ := h
    exact hj.1.1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  have hPX := v_power_mem_l I hV hδ (hj.input_mem_of_pairMember hjD) hP
  have hQX := v_power_mem_l I hV hδ hPX hQ
  have hUP : M.MemberSubset U P := fun s hs => (hP s).mpr ((hU s).mp hs).1
  have hUX := hX Q hQX U ((hQ U).mpr hUP)
  obtain ⟨R, hRX, hκR, hPR⟩ := v_joint_bound_l I hV hc.source hPX
  obtain ⟨U', _, hjU⟩ := hj.2.2 U hUX
  intro μ hμ F hF
  have hFX : M.mem F X := v_relation_mem_l I hV hδ hRX (fun p hp => by
    obtain ⟨i, hi, s, hs, hc'⟩ := hF.1 p hp
    exact ⟨i, hκR i (hc.ordinal.transitive μ hμ i hi), s, hPR s (hUP s hs), hc'⟩)
  obtain ⟨F', _, hjF⟩ := hj.2.2 F hFX
  have hjμ := hc.fixed μ hμ
  have hF' := (spred_function_l I hZF hω h hX hY hjμ hjU hjF).mp hF
  let ρ : Env M 3 := ⟨Fin.cases F (Fin.cases U (fun _ => μ)), fun _ => μ⟩
  let ψ : UnarySchema 3 := { body := ed_all_m (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨r, hr⟩ := ZF.separation_exists_d hZF ψ ρ D
  have hr' x : M.mem x r ↔ M.mem x D ∧ Ed_all_d μ U F x :=
    (hr x).trans (and_congr_right fun _ => ed_all_sat_l hZF.1 _ _ _ _ _)
  have hrD : M.MemberSubset r D := fun x hx => ((hr' x).mp hx).1
  obtain ⟨r', _, hjr⟩ := hj.2.2 r (hX P hPX r ((hP r).mpr hrD))
  let φ : Formula 1 5 := Formula.forallMem (.bound 4) (.iff (.mem .newest (.bound 1))
    (ed_all_m (.bound 4) (.bound 3) (.bound 2) .newest))
  have tr := spred_delta_l I hZF hω h hX hY φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (ed_all_delta_l ..)))
    ⟨Fin.cases r (Fin.cases F (Fin.cases U (Fin.cases μ (fun _ => D)))), fun _ => D⟩
    ⟨Fin.cases r' (Fin.cases F' (Fin.cases U' (Fin.cases μ (fun _ => D')))), fun _ => D'⟩
    (Fin.cases hjr (Fin.cases hjF (Fin.cases hjU (Fin.cases hjμ (fun _ => hjD)))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, ed_all_sat_l hZF.1] at tr
  have target : ∀ x, M.mem x D' → (M.mem x r' ↔ Ed_all_d μ U' F' x) :=
    tr.mp (fun x hx => (hr' x).trans ⟨And.right, fun ha => ⟨hx, ha⟩⟩)
  refine ⟨r, (hU r).mpr ⟨hrD, r', hjr, (target a ha).mpr ?_⟩, hr'⟩
  intro i hi s hs his
  obtain ⟨t, ht, hit⟩ := hF.2.1 i hi
  obtain ⟨_, t', hjt, hat⟩ := (hU t).mp ht
  have ht' := (ed_member_l I hZF hω h hX hY hjt hjU).mp ht
  have hjI := hc.fixed i (hc.ordinal.transitive μ hμ i hi)
  have hit' := (spred_entry_l I hZF hω h hX hY hjI hjt hjF).mp hit
  exact (hF'.2.2 i hi s hs t' ht' his hit').symm ▸ hat

omit hX hY hω h in
/-- 武丁基数提供实际非主 κ 完备超滤； κ 完备性不作为假设传入。 -/
theorem wd_complete_ultrafilter_l {δ α} (hd : Woodin_d I δ) (hα : M.mem α δ) :
    ∃ ω κ U, M.IsOmega ω ∧ M.mem ω κ ∧ M.mem α κ ∧ M.mem κ δ ∧ M.IsOrdinal κ ∧ FilterZF.Maximal_d (ℳ := M) κ U ∧
      Ed_nonprincipal_d U ∧ Ed_complete_d κ κ U := by
  obtain ⟨ω, X, hω, _, hr, _, hV, hd⟩ := hd
  obtain ⟨F, hF⟩ := hr.2.1
  have hl := hF.1
  obtain ⟨β, hβ, hαβ⟩ := hl.2.2 α hα
  obtain ⟨ν, hν, hβν⟩ := hl.2.2 β hβ
  have hβX : M.MemberSubset β X := fun x hx => ZF.v_ordinal_subset_l I hZF hV x (hl.1.transitive β hβ x hx)
  obtain ⟨κ, hκδ, hk⟩ := hd β hβX
  obtain ⟨N, B, j, W, k, hN, _, _, hW, _, hj, hc, hνk, trace⟩ := hk ν hν
  have hn : ¬ M.mem κ β := by
    intro hκβ
    have hkB := (spred_predicate_l I hZF hω hj hc.image).mp hκβ
    have hβB := spred_transitive_l I hZF hω hj hN (hl.1.mem hβ).transitive k hkB β
      (hc.ordinal_image.transitive ν hνk β hβν)
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) β ((trace β (ZF.v_ordinal_mem_l I hZF hW hβν)).mpr hβB)
  have hακ : M.mem α κ := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 (hl.1.mem hα) hc.ordinal
        (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) α κ) with he | he | he
    · exact (hn ((hZF.1.eq_of_same_members α κ he) ▸ hαβ)).elim
    · exact he
    · exact (hn ((hl.1.mem hβ).transitive α hαβ κ he)).elim
  have hκ : M.mem κ k := by
    have hs : M.MemberSubset κ k := fun x hx =>
      (ed_member_l I hZF hω hj (v_transitive_l I hV) hN (hc.fixed x hx) hc.image).mp hx
    exact Structure.IsOrdinal.mem_of_properSubset hZF.1 hc.ordinal hc.ordinal_image
      ⟨hs, fun he => hc.moved (hZF.1.eq_of_same_members κ k he)⟩
      (KP.difference_exists_d (ZF.modelsKP hZF) κ k)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  obtain ⟨U, hU, hu, hn⟩ := ed_critical_measure_l I hZF hω hj (v_transitive_l I hV)
    hN hc hκ hP (v_power_mem_l I hV hF.1 hc.source hP)
  exact ⟨ω, κ, U, hω, ed_critical_omega_l I hZF hω hj (v_transitive_l I hV) hN hc,
    hακ, hκδ, hc.ordinal, hu, hn, ed_complete_l I hZF hω hj hN hV hl hc hc.image hκ hU⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁基数以下的实际可测基数

非主 κ 完备超滤迫使 κ 为初始序数：若较短序数枚举 κ，
各枚举值的补单点集都测度一，但它们的短交为空，矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_range_complement_l (hZF : M.Models ZF) {κ U μ f : M.Domain}
    (hU : FilterZF.Maximal_d (ℳ := M) κ U) (hn : Ed_nonprincipal_d U) (hc : Ed_complete_d κ κ U)
    (hμ : M.mem μ κ) (hf : M.IsSetFunctionFromTo I f μ κ) :
    ∃ r, M.mem r U ∧ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ ∃ i, M.mem i μ ∧ M.PairMember I i x f := by
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => κ), fun _ => κ⟩
  let φ : BinarySchema 2 := { body := .forallE (.iff (.mem .newest (.bound 1))
    (.conj (.mem .newest (.bound 4)) (.neg (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))))) }
  have sat i r : φ.denote ρ i r ↔ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ M.PairMember I i x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨P, power⟩ := ZF.exists_powerSet hZF κ
  have total i (hi : M.mem i μ) : ∃ r, φ.denote ρ i r ∧ M.mem r U := by
    obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
    obtain ⟨s, hs⟩ := KP.exists_singleton (ZF.modelsKP hZF) x
    obtain ⟨r, hr⟩ := KP.difference_exists_d (ZF.modelsKP hZF) s κ
    have eq y : M.mem y s ↔ M.PairMember I i y f :=
      (hs y).trans ⟨fun hy => hy.symm ▸ hix, fun hy => hf.1.2 i y x hy hix⟩
    refine ⟨r, (sat i r).mpr (fun y => (hr y).trans (and_congr_right fun _ => not_congr (eq y))), ?_⟩
    exact (FilterZF.maximal_decides_d (ZF.modelsKP hZF) power hU (fun y hy => (hs y).mp hy ▸ hx) hr).elim
      (fun h => (hn x s hs h).elim) id
  have unique i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s :=
    hZF.1.eq_of_same_members r s (fun x => ((sat i r).mp hr x).trans ((sat i s).mp hs x).symm)
  obtain ⟨g, hg, hgp⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    (fun i hi => (total i hi).imp fun _ hr => hr.1)
    (fun i _ r s hr hs => unique i r s hr hs) (fun i r hi hr => by
      obtain ⟨s, hs, hsU⟩ := total i hi
      exact (unique i s r hs hr) ▸ hsU)
  obtain ⟨r, hrU, hr⟩ := hc μ hμ g (fn0_of_function_l (ZF.modelsKP hZF) hg)
  refine ⟨r, hrU, fun x => (hr x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun ⟨i, hi, hix⟩ => ?_⟩
    obtain ⟨s, hs, his⟩ := hg.2.2 i hi
    exact (((sat i s).mp ((hgp i s).mp his).2 x).mp (hall i hi s hs his)).2 hix
  · rintro ⟨hx, no⟩
    exact ⟨hx, fun i hi s _ his => (((sat i s).mp ((hgp i s).mp his).2 x)).mpr
      ⟨hx, fun hix => no ⟨i, hi, hix⟩⟩⟩

/-- 短枚举的补集仍测度一，故 κ 不可能由较短序数枚举。 -/
theorem ed_cardinal_l (hZF : M.Models ZF) {κ U} (hκ : M.IsOrdinal κ)
    (hU : FilterZF.Maximal_d (ℳ := M) κ U) (hn : Ed_nonprincipal_d U) (hc : Ed_complete_d κ κ U) :
    M.IsCardinal I κ := by
  refine ⟨hκ, fun μ hμ ⟨f, hf⟩ => ?_⟩
  obtain ⟨r, hr, rs⟩ := ed_range_complement_l I hZF hU hn hc hμ hf.1.1
  obtain ⟨x, hx⟩ := hU.2.1 r hr
  exact ((rs x).mp hx).2 (hf.2 x ((rs x).mp hx).1)

def Measurable_d (κ : M.Domain) : Prop := M.IsCardinal I κ ∧ ∃ ω U, M.IsOmega ω ∧ M.mem ω κ ∧
  FilterZF.Maximal_d (ℳ := M) κ U ∧ Ed_nonprincipal_d U ∧ Ed_complete_d κ κ U

def measurable_m {d} (κ : Term d) : Formula 1 d := .conj (Formula.isCardinal 𝒞 κ)
  (.existsE (.existsE (.conj (Formula.isOmega (.bound 1)) (.conj (.mem (.bound 1) κ.weaken.weaken)
    (.conj (FilterZF.maximal_m κ.weaken.weaken .newest)
      (.conj (ed_nonprincipal_m .newest) (ed_complete_m κ.weaken.weaken κ.weaken.weaken .newest)))))))
derive_free_closed measurable_m

theorem measurable_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ : Term d) :
    Formula.satisfies ρ (measurable_m (𝒞 := 𝒞) κ) ↔ Measurable_d I (κ.eval ρ) := by
  simp only [measurable_m, Measurable_d, Formula.satisfies_conj_iff, Formula.satisfies_isCardinal_iff I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff,
    FilterZF.maximal_sat_d, ed_nonprincipal_sat_l hE, ed_complete_sat_l hE, Definitional.Term.eval_weaken]
  rfl

/-- 武丁基数以下的可测基数无界，测度由原定义中的实际嵌入构造。 -/
theorem woodin_measurable_above_l (hZF : M.Models ZF) {δ α} (hδ : Woodin_d I δ) (hα : M.mem α δ) :
    ∃ κ, M.mem α κ ∧ M.mem κ δ ∧ Measurable_d I κ := by
  obtain ⟨ω, κ, U, hω, hωκ, hακ, hκδ, hκ, hU, hn, hc⟩ := wd_complete_ultrafilter_l I hZF hδ hα
  exact ⟨κ, hακ, hκδ, ed_cardinal_l I hZF hκ hU hn hc, ω, U, hω, hωκ, hU, hn, hc⟩

theorem woodin_proper_measurables_l (hZF : M.Models ZF) (h : Wd_proper_d I) :
    ∀ α, M.IsOrdinal α → ∃ κ, M.mem α κ ∧ Measurable_d I κ := by
  intro α hα
  obtain ⟨δ, hαδ, hδ⟩ := h α hα
  obtain ⟨κ, hακ, _, hκ⟩ := woodin_measurable_above_l I hZF hδ hαδ
  exact ⟨κ, hακ, hκ⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完备非主超滤排除小幂集中的长单射

逐坐标选取测度一的真假纤维，再取少于 κ 个纤维的交。
交内任意两点的子集像完全相同；若原图为单射，交就是单点集，矛盾。
真假选择由超滤的唯一决定及原替代构造，不使用选择公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_power_injection_l (hZF : M.Models ZF) {κ U μ P : M.Domain}
    (hU : FilterZF.Maximal_d (ℳ := M) κ U) (hn : Ed_nonprincipal_d U) (hc : Ed_complete_d κ κ U)
    (hμ : M.mem μ κ) (power : M.IsPowerSetOf P μ) : ¬ M.CardinalLessOrEqual I κ P := by
  classical
  rintro ⟨f, hf⟩
  let hit i x := ∃ A, M.PairMember I x A f ∧ M.mem i A
  let ρ : Env M 3 := ⟨Fin.cases f (Fin.cases κ (fun _ => U)), fun _ => κ⟩
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 4)) (.disj
      (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 4))
        (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem (.bound 3) .newest))))))
      (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 4))
        (.neg (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem (.bound 3) .newest)))))))) }
  have read i s : φ.denote ρ i s ↔ M.mem s U ∧
      ((∀ x, M.mem x s ↔ M.mem x κ ∧ hit i x) ∨ (∀ x, M.mem x s ↔ M.mem x κ ∧ ¬ hit i x)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff]; rfl
  obtain ⟨Q, subsets⟩ := ZF.exists_powerSet hZF κ
  have total i (_ : M.mem i μ) : ∃ s, φ.denote ρ i s := by
    let θ : UnarySchema 2 := {
      body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3)) (.mem (.bound 2) .newest)) }
    obtain ⟨s, ss⟩ := ZF.separation_exists_d hZF θ ⟨Fin.cases i (fun _ => f), fun _ => κ⟩ κ
    have row x : M.mem x s ↔ M.mem x κ ∧ hit i x := by
      simpa only [θ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff] using! ss x
    by_cases hs : M.mem s U
    · exact ⟨s, (read i s).mpr ⟨hs, Or.inl row⟩⟩
    obtain ⟨t, ts⟩ := KP.difference_exists_d (ZF.modelsKP hZF) s κ
    have ht := (FilterZF.maximal_decides_d (ZF.modelsKP hZF) subsets hU (fun x hx => ((row x).mp hx).1) ts).resolve_left hs
    exact ⟨t, (read i t).mpr ⟨ht, Or.inr (fun x => (ts x).trans
      ⟨fun ⟨hx, no⟩ => ⟨hx, fun hi => no ((row x).mpr ⟨hx, hi⟩)⟩,
        fun ⟨hx, no⟩ => ⟨hx, fun hs => no ((row x).mp hs).2⟩⟩)⟩⟩
  have apart i s t (hs : M.mem s U) (ht : M.mem t U)
      (left : ∀ x, M.mem x s ↔ M.mem x κ ∧ hit i x)
      (right : ∀ x, M.mem x t ↔ M.mem x κ ∧ ¬ hit i x) : False := by
    obtain ⟨r, hr, rs, rt⟩ := hU.1.2.2.2 s t hs ht
    obtain ⟨x, hx⟩ := hU.2.1 r hr
    exact ((right x).mp (rt x hx)).2 ((left x).mp (rs x hx)).2
  have unique i s t (hs : φ.denote ρ i s) (ht : φ.denote ρ i t) : s = t := by
    obtain ⟨hs, left⟩ := (read i s).mp hs
    obtain ⟨ht, right⟩ := (read i t).mp ht
    rcases left with left | left <;> rcases right with right | right
    · exact hZF.1.eq_of_same_members s t (fun x => (left x).trans (right x).symm)
    · exact (apart i s t hs ht left right).elim
    · exact (apart i t s ht hs right left).elim
    · exact hZF.1.eq_of_same_members s t (fun x => (left x).trans (right x).symm)
  obtain ⟨g, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    total (fun i _ => unique i) (fun i s _ hs => ((read i s).mp hs).1)
  obtain ⟨r, hr, rs⟩ := hc μ hμ g (fn0_of_function_l (ZF.modelsKP hZF) gf)
  have decode i x A (hx : M.PairMember I x A f) : hit i x ↔ M.mem i A :=
    ⟨fun ⟨B, hb, hi⟩ => hf.1.1.2 x B A hb hx ▸ hi, fun hi => ⟨A, hx, hi⟩⟩
  have same x y (hx : M.mem x r) (hy : M.mem y r) : x = y := by
    obtain ⟨hxκ, allx⟩ := (rs x).mp hx
    obtain ⟨hyκ, ally⟩ := (rs y).mp hy
    obtain ⟨A, hA, hxA⟩ := hf.1.2.2 x hxκ
    obtain ⟨B, hB, hyB⟩ := hf.1.2.2 y hyκ
    have eq : A = B := hZF.1.eq_of_same_members A B (fun i => by
      by_cases hi : M.mem i μ
      · obtain ⟨s, hs, his⟩ := gf.2.2 i hi
        have xx := allx i hi s hs his
        have yy := ally i hi s hs his
        rcases ((read i s).mp ((gs i s).mp his).2).2 with row | row
        · exact iff_of_true ((decode i x A hxA).mp ((row x).mp xx).2) ((decode i y B hyB).mp ((row y).mp yy).2)
        · exact iff_of_false (fun h => ((row x).mp xx).2 ((decode i x A hxA).mpr h))
            (fun h => ((row y).mp yy).2 ((decode i y B hyB).mpr h))
      · exact iff_of_false (fun h => hi ((power A).mp hA i h)) (fun h => hi ((power B).mp hB i h)))
    exact hf.2 x y A hxA (eq.symm ▸ hyB)
  obtain ⟨x, hx⟩ := hU.2.1 r hr
  exact hn x r (fun y => ⟨fun hy => same y x hy hx, fun eq => eq.symm ▸ hx⟩) hr

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 强嵌入下的共同分支回拉

对局及有限前缀均为内部函数图。存在贯穿每个内部长度的分支是一个实际 Σ₁ 断言；
目标侧分支属于嵌入载体时，全内部初等性将其回拉到原秩层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Eb_d (ω D T f : M.Domain) : Prop := Fn0_d ω D f ∧ ∀ n, M.mem n ω →
  ∃ s, M.mem s T ∧ Fn0_d n D s ∧ M.MemberSubset s f

def eb_m {d} (ω D T f : Term d) : Formula 1 d := .conj (fn0_m ω D f)
  (Formula.forallMem ω (Formula.existsMem T.weaken (.conj (fn0_m (.bound 1) D.weaken.weaken .newest)
    (Formula.subset .newest f.weaken.weaken))))
derive_free_closed eb_m

theorem eb_delta_l {d} (ω D T f : Term d) : (eb_m ω D T f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.atom _ _ _))))

theorem eb_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D T f : Term d) :
    Formula.satisfies ρ (eb_m ω D T f) ↔ Eb_d (ω.eval ρ) (D.eval ρ) (T.eval ρ) (f.eval ρ) := by
  simp only [eb_m, Eb_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem eb_mono_l {ω D E T f} (hDE : M.MemberSubset D E) (h : Eb_d ω D T f) : Eb_d ω E T f :=
  ⟨h.1.mono_target_l hDE, fun n hn => (h.2 n hn).imp fun _ hs => ⟨hs.1, hs.2.1.mono_target_l hDE, hs.2.2⟩⟩

theorem ed_branch_pull_l (hZF : M.Models ZF) {ω X A Y B j D D' T T' f}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hjω : M.PairMember I ω ω j) (hjD : M.PairMember I D D' j) (hjT : M.PairMember I T T' j)
    (hfY : M.mem f Y) (hf : Eb_d ω D' T' f) : ∃ g, M.mem g X ∧ Eb_d ω D T g := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  have h : Spred_emb_d I ω X A Y B j := ⟨c, R, d, S, hx, hy, hj⟩
  let hn : Nonempty {x // M.mem x X} := hx.1.2.1.elim (fun x hx => ⟨⟨x, hx⟩⟩)
  let hm : Nonempty {x // M.mem x Y} := hy.1.2.1.elim (fun x hx => ⟨⟨x, hx⟩⟩)
  let ρ : Env (rt_model_l X hn) 3 := ⟨Fin.cases ⟨T, hj.1.1.input_mem_of_pairMember hjT⟩
    (Fin.cases ⟨D, hj.1.1.input_mem_of_pairMember hjD⟩ (fun _ => ⟨ω, hj.1.1.input_mem_of_pairMember hjω⟩)),
    fun _ => ⟨ω, hj.1.1.input_mem_of_pairMember hjω⟩⟩
  let η : Env (rt_model_l Y hm) 3 := ⟨Fin.cases ⟨T', hj.1.1.output_mem_of_pairMember hjT⟩
    (Fin.cases ⟨D', hj.1.1.output_mem_of_pairMember hjD⟩ (fun _ => ⟨ω, hj.1.1.output_mem_of_pairMember hjω⟩)),
    fun _ => ⟨ω, hj.1.1.output_mem_of_pairMember hjω⟩⟩
  let φ : Formula 1 4 := eb_m (.bound 3) (.bound 2) (.bound 1) .newest
  have hd : φ.IsDelta0 := eb_delta_l ..
  have hc : φ.FreeClosed := eb_m_freeClosed _ _ _ _ rfl rfl rfl rfl
  have tr := spred_source_l I hZF hω h hn hm (.existsE φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hc) ρ η (Fin.cases hjT (Fin.cases hjD (fun _ => hjω)))
  have ht : Formula.satisfies (η.push ⟨f, hfY⟩) φ :=
    (rt_model_delta_l hY hm hd _).mpr ((eb_sat_l hZF.1 _ _ _ _ _).mpr hf)
  obtain ⟨g, hg⟩ := (Formula.satisfies_exists_iff ρ φ).mp (tr.mpr ((Formula.satisfies_exists_iff η φ).mpr ⟨⟨f, hfY⟩, ht⟩))
  exact ⟨g.val, g.property, (eb_sat_l hZF.1 _ _ _ _ _).mp ((rt_model_delta_l hX hn hd _).mp hg)⟩

/-- 先界定需要覆盖的实际集合，再选择足够强的嵌入。 -/
theorem wd_cover_embedding_l (hZF : M.Models ZF) {ω δ X A κ L G}
    (hV : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (hk : Wd_strong_d I ω δ X A κ) (hL : M.mem L δ) (hGX : M.mem G X) :
    ∃ ν N B j W k, Wd_witness_d I ω δ X A κ ν N B j W k ∧ M.mem L ν ∧ M.mem L k ∧ M.mem G N := by
  obtain ⟨γ, V, hγ, hVγ, hGV⟩ := (ZF.v_limit_mem_l I hZF hV hδ.2.2 G).mp hGX
  obtain ⟨η, hη, hLη⟩ := hδ.2.2 L hL
  have bound : ∃ ν, M.mem ν δ ∧ M.mem L ν ∧ M.MemberSubset γ ν := by
    rcases hδ.1.wellOrder.linear.compare γ hγ η hη with he | he | he
    · exact ⟨η, hη, hLη, fun x hx => (he x).mp hx⟩
    · exact ⟨η, hη, hLη, (hδ.1.mem hη).transitive γ he⟩
    · exact ⟨γ, hγ, (hδ.1.mem hγ).transitive η he L hLη, fun _ hx => hx⟩
  obtain ⟨ν, hν, hLν, hγν⟩ := bound
  obtain ⟨N, B, j, W, k, hw⟩ := hk ν hν
  obtain ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩ := hw
  have hGN := hWN G (ZF.v_mono_l I hZF hVγ hW hγν G hGV)
  have hLk := hc.ordinal_image.transitive ν hνk L hLν
  exact ⟨ν, N, B, j, W, k, ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩, hLν, hLk, hGN⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际派生测度族与投影协调

对每个种子同时收集唯一的派生超滤，形成模型内函数图。
若 j(p)(b)=a，则 p 的逆像把 a 处的测度精确拉到 b 处；协调性由初等性证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ef_family_d (j D S F : M.Domain) : Prop := M.IsSetFunction I F ∧ M.IsDomainOf I S F ∧
  ∀ a U, M.PairMember I a U F ↔ M.mem a S ∧ Ed_filter_d I j a D U

def ef_family_m {d} (j D S F : Term d) : Formula 1 d :=
  .conj (Formula.isFunction 𝒞 F) (.conj (Formula.isDomain 𝒞 S F) (.forallE (.forallE
    (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (.conj (.mem (.bound 1) S.weaken.weaken) (ed_filter_m (𝒞 := 𝒞) j.weaken.weaken (.bound 1) D.weaken.weaken .newest))))))
derive_free_closed ef_family_m

theorem ef_family_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j D S F : Term d) :
    Formula.satisfies ρ (ef_family_m (𝒞 := 𝒞) j D S F) ↔
      Ef_family_d I (j.eval ρ) (D.eval ρ) (S.eval ρ) (F.eval ρ) := by
  simp only [ef_family_m, Ef_family_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, ed_filter_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem ef_family_exists_l (hZF : M.Models ZF) (j D S : M.Domain) : ∃ F, Ef_family_d I j D S F := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  let ρ : Env M 2 := ⟨Fin.cases D (fun _ => j), fun _ => D⟩
  let φ : BinarySchema 2 := { body := ed_filter_m (𝒞 := 𝒞) (.bound 3) (.bound 1) (.bound 2) .newest }
  have sat a U : φ.denote ρ a U ↔ Ed_filter_d I j a D U := ed_filter_sat_l I _ _ _ _ _
  obtain ⟨F, hf, hp⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := S) (target := Q) (fun a _ => (ed_filter_exists_l I hZF j a D).imp fun U hU => (sat a U).mpr hU)
    (fun a _ U V hU hV => ed_filter_unique_l I hZF.1 ((sat a U).mp hU) ((sat a V).mp hV))
    (fun a U _ hU => (hQ U).mpr fun s hs => (hP s).mpr (((sat a U).mp hU s).mp hs).1)
  exact ⟨F, hf.1, hf.2.1, fun a U => (hp a U).trans (and_congr_right fun _ => sat a U)⟩

theorem ef_family_ultra_l (hZF : M.Models ZF) {ω X A Y B j D D' P S F}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hP : M.IsPowerSetOf P D) (hPX : M.mem P X) (hjD : M.PairMember I D D' j)
    (hS : M.MemberSubset S D') (hF : Ef_family_d I j D S F) {a U} (ha : M.PairMember I a U F) :
    FilterZF.Maximal_d (ℳ := M) D U := by
  obtain ⟨haS, hU⟩ := (hF.2.2 a U).mp ha
  obtain ⟨V, hV, hv⟩ := ed_ultrafilter_l I hZF hω h hX hY hP hPX hjD (hS a haS)
  exact ed_filter_unique_l I hZF.1 hV hU ▸ hv

/-- 任何实际投影的逆像都满足派生测度协调方程。 -/
theorem ed_projection_l (hZF : M.Models ZF) {ω δ X C Y E j D D' H H' p p' a b A A' U V}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X C Y E j) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (hY : M.TransitiveSet Y) (hD : M.PairMember I D D' j) (hH : M.PairMember I H H' j)
    (hp : M.PairMember I p p' j) (hf : Fn0_d H D p) (hab : Rd_entry_d b a p')
    (hA : M.MemberSubset A D) (hjA : M.PairMember I A A' j)
    (hU : Ed_filter_d I j a D U) (hV : Ed_filter_d I j b H V) :
    ∃ Z, (∀ x, M.mem x Z ↔ M.mem x H ∧ ∃ y, M.mem y A ∧ Rd_entry_d x y p) ∧
      (M.mem Z V ↔ M.mem A U) := by
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hf' := (spred_function_l I hZF hω h ht hY hH hD hp).mp hf
  let ρ : Env M 2 := ⟨Fin.cases p (fun _ => A), fun _ => A⟩
  let ψ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨Z, hz⟩ := ZF.separation_exists_d hZF ψ ρ H
  have spec x : M.mem x Z ↔ M.mem x H ∧ ∃ y, M.mem y A ∧ Rd_entry_d x y p := by
    rw [hz x]; simp only [ψ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1]; rfl
  have sub : M.MemberSubset Z H := fun x hx => ((spec x).mp hx).1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF H
  obtain ⟨Z', _, hjZ⟩ := hj.2.2 Z (ht P (v_power_mem_l I hX hδ (hj.input_mem_of_pairMember hH) hP) Z ((hP Z).mpr sub))
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (.iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (rd_entry0_m (.bound 1) .newest (.bound 3))))
  have tr := spred_delta_l I hZF hω h ht hY φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (.existsMem _ (rd_entry0_delta_l ..))))
    ⟨Fin.cases Z (Fin.cases p (Fin.cases A (fun _ => H))), fun _ => H⟩
    ⟨Fin.cases Z' (Fin.cases p' (Fin.cases A' (fun _ => H'))), fun _ => H'⟩
    (Fin.cases hjZ (Fin.cases hp (Fin.cases hjA (fun _ => hH))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] at tr
  have target : ∀ x, M.mem x H' → (M.mem x Z' ↔ ∃ y, M.mem y A' ∧ Rd_entry_d x y p') :=
    tr.mp (fun x hx => (spec x).trans ⟨And.right, fun hy => ⟨hx, hy⟩⟩)
  refine ⟨Z, spec, (ed_filter_member_l I hj.1 hV sub hjZ).trans
    (((target b (hf'.bound_l hab).1).trans ?_).trans (ed_filter_member_l I hj.1 hU hA hjA).symm)⟩
  exact ⟨fun ⟨y, hy, hby⟩ => (hf'.2.2 b (hf'.bound_l hab).1 y (hf'.bound_l hby).2
    a (hf'.bound_l hab).2 hby hab) ▸ hy, fun ha => ⟨a, ha, hab⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 派生扩展器所需的共同纤维可数完备性

第 n 层只含长度 n 的内部有限列。各层之并保留共同纤维；回拉并集上的分支后，
函数定义域的唯一性把每个前缀精确归还到原第 n 层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ef_levels_d (ω D H : M.Domain) : Prop := (∃ P, Fn0_d ω P H) ∧
  ∀ n A, Rd_entry_d n A H → ∀ s, M.mem s A → Fn0_d n D s

def Ef_fiber_d (ω D H f : M.Domain) : Prop := Fn0_d ω D f ∧ ∀ n, M.mem n ω →
  ∃ A s, Rd_entry_d n A H ∧ M.mem s A ∧ Fn0_d n D s ∧ M.MemberSubset s f

def Ef_image_fiber_d (j ω D H f : M.Domain) : Prop := Fn0_d ω D f ∧ ∀ n, M.mem n ω →
  ∃ A A' s, Rd_entry_d n A H ∧ M.PairMember I A A' j ∧ M.mem s A' ∧ Fn0_d n D s ∧ M.MemberSubset s f

def ef_levels_m {d} (ω D H : Term d) : Formula 1 d :=
  .conj (.existsE (fn0_m ω.weaken .newest H.weaken)) (.forallE (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest H.weaken.weaken)
      (Formula.forallMem .newest (fn0_m (.bound 2) D.weaken.weaken.weaken .newest)))))
derive_free_closed ef_levels_m

def ef_fiber_m {d} (ω D H f : Term d) : Formula 1 d := .conj (fn0_m ω D f)
  (Formula.forallMem ω (.existsE (.existsE (.conj
    (rd_entry0_m (.bound 2) (.bound 1) H.weaken.weaken.weaken) (.conj (.mem .newest (.bound 1))
      (.conj (fn0_m (.bound 2) D.weaken.weaken.weaken .newest) (Formula.subset .newest f.weaken.weaken.weaken)))))))
derive_free_closed ef_fiber_m

def ef_image_fiber_m {d} (j ω D H f : Term d) : Formula 1 d := .conj (fn0_m ω D f)
  (Formula.forallMem ω (.existsE (.existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 2) H.weaken.weaken.weaken.weaken) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) j.weaken.weaken.weaken.weaken) (.conj (.mem .newest (.bound 1))
        (.conj (fn0_m (.bound 3) D.weaken.weaken.weaken.weaken .newest)
          (Formula.subset .newest f.weaken.weaken.weaken.weaken)))))))))
derive_free_closed ef_image_fiber_m

theorem ef_levels_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D H : Term d) :
    Formula.satisfies ρ (ef_levels_m ω D H) ↔ Ef_levels_d (ω.eval ρ) (D.eval ρ) (H.eval ρ) := by
  simp only [ef_levels_m, Ef_levels_d, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    fn0_sat_l hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hE,
    Formula.satisfies_forallMem_iff, Definitional.Term.eval_weaken]
  rfl

theorem ef_fiber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D H f : Term d) :
    Formula.satisfies ρ (ef_fiber_m ω D H f) ↔ Ef_fiber_d (ω.eval ρ) (D.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [ef_fiber_m, Ef_fiber_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]
  rfl

theorem ef_image_fiber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j ω D H f : Term d) :
    Formula.satisfies ρ (ef_image_fiber_m (𝒞 := 𝒞) j ω D H f) ↔
      Ef_image_fiber_d I (j.eval ρ) (ω.eval ρ) (D.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [ef_image_fiber_m, Ef_image_fiber_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hE, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

/-- 共同纤维回拉给出整个层族的可数完备性，强于逐个测度的可数完备性。 -/
theorem ef_common_fiber_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L G H f}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hLk : M.MemberSubset L k) (hG : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G ω L)
    (hGY : M.mem G Y) (hH : Ef_levels_d ω κ H) (hf : Ef_image_fiber_d I j ω L H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  have ht := v_transitive_l I hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨P, hHP⟩ := hH.1
  have hFn := fn0_function_l (ZF.modelsKP hZF) hHP
  obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF (kp_pair_l (ZF.modelsKP hZF)) hFn.1 hFn.2.1
  obtain ⟨T, hT⟩ := KP.exists_union (ZF.modelsKP hZF) R
  have spec s : M.mem s T ↔ ∃ n A, Rd_entry_d n A H ∧ M.mem s A := by
    rw [hT s]
    exact ⟨fun ⟨A, hA, hs⟩ => ((hR A).mp hA).elim fun n hn => ⟨n, A, hn, hs⟩,
      fun ⟨n, A, hn, hs⟩ => ⟨A, (hR A).mpr ⟨n, hn⟩, hs⟩⟩
  have hTX : M.mem T X := v_relations_mem_l I hX hδ hc.source (fun s hs p hp => by
    obtain ⟨n, A, hn, hsA⟩ := (spec s).mp hs
    obtain ⟨i, hi, a, ha, hp⟩ := (hH.2 n A hn s hsA).1 p hp
    exact ⟨i, hc.ordinal.transitive ω hωκ i (hω.transitive (ZF.modelsKP hZF) n (hHP.bound_l hn).1 i hi), a, ha, hp⟩)
  obtain ⟨T', _, hjT⟩ := hj.2.2 T hTX
  have branch : Eb_d ω L T' f := by
    refine ⟨hf.1, fun n hn => ?_⟩
    obtain ⟨A, A', s, hA, hjA, hs, hsFn, hsf⟩ := hf.2 n hn
    have sub : M.MemberSubset A T := fun t ht => (spec t).mpr ⟨n, A, hA, ht⟩
    exact ⟨s, (ed_subset_l I hZF hω h ht hY hjA hjT).mp sub s hs, hsFn, hsf⟩
  obtain ⟨g, hgX, hg⟩ := ed_branch_pull_l I hZF hω h ht hY (hc.fixed ω hωκ) hc.image hjT
    (hY G hGY f ((hG f).mpr (fn0_function_l (ZF.modelsKP hZF) hf.1))) (eb_mono_l hLk branch)
  refine ⟨g, hgX, hg.1, fun n hn => ?_⟩
  obtain ⟨s, hs, hsFn, hsg⟩ := hg.2 n hn
  obtain ⟨m, A, hmA, hsA⟩ := (spec s).mp hs
  have eq := hsFn.domain_eq_l hZF.1 (hH.2 m A hmA s hsA)
  exact ⟨A, s, eq.symm ▸ hmA, hsA, hsFn, hsg⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部有限支撑上的实际测度图

长度由支撑函数的定义域唯一确定。对 a:n→L，在 κ^n 上取种子 a 派生的测度；
全部分量同时收集成内部集合函数，不在元层逐个选择测度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Es_value_d (j κ L a U : M.Domain) : Prop := ∃ n D, Fn0_d n L a ∧
  (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧ Ed_filter_d I j a D U

def es_value_m {d} (j κ L a U : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (fn0_m (.bound 1) L.weaken.weaken a.weaken.weaken) (.conj
    (.forallE (.iff (.mem .newest (.bound 1)) (fn0_m (.bound 2) κ.weaken.weaken.weaken .newest)))
    (ed_filter_m (𝒞 := 𝒞) j.weaken.weaken a.weaken.weaken .newest U.weaken.weaken))))
derive_free_closed es_value_m

theorem es_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j κ L a U : Term d) :
    Formula.satisfies ρ (es_value_m (𝒞 := 𝒞) j κ L a U) ↔
      Es_value_d I (j.eval ρ) (κ.eval ρ) (L.eval ρ) (a.eval ρ) (U.eval ρ) := by
  simp only [es_value_m, Es_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    ed_filter_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem es_value_unique_l (hE : Extensional M) {j κ L a U V}
    (hU : Es_value_d I j κ L a U) (hV : Es_value_d I j κ L a V) : U = V := by
  obtain ⟨n, D, hn, hD, hU⟩ := hU
  obtain ⟨m, E, hm, hS, hV⟩ := hV
  have he := hn.domain_eq_l hE hm
  subst m
  have he := hE.eq_of_same_members D E (fun s => (hD s).trans (hS s).symm)
  subst E
  exact ed_filter_unique_l I hE hU hV

def Es_family_d (j κ L S F : M.Domain) : Prop := M.IsSetFunction I F ∧ M.IsDomainOf I S F ∧
  ∀ a U, M.PairMember I a U F ↔ M.mem a S ∧ Es_value_d I j κ L a U

def es_family_m {d} (j κ L S F : Term d) : Formula 1 d :=
  .conj (Formula.isFunction 𝒞 F) (.conj (Formula.isDomain 𝒞 S F) (.forallE (.forallE
    (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken) (.conj (.mem (.bound 1) S.weaken.weaken)
      (es_value_m (𝒞 := 𝒞) j.weaken.weaken κ.weaken.weaken L.weaken.weaken (.bound 1) .newest))))))
derive_free_closed es_family_m

theorem es_family_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j κ L S F : Term d) :
    Formula.satisfies ρ (es_family_m (𝒞 := 𝒞) j κ L S F) ↔
      Es_family_d I (j.eval ρ) (κ.eval ρ) (L.eval ρ) (S.eval ρ) (F.eval ρ) := by
  simp only [es_family_m, Es_family_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, es_value_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem es_family_exists_l (hZF : M.Models ZF) {ω L S} (hω : M.IsOmega ω)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (j κ : M.Domain) :
    ∃ F, Es_family_d I j κ L S F := by
  let K := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨T, hT⟩ := ZF.fseq_space_exists_l K hZF hω κ
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF T
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  let ρ : Env M 3 := ⟨Fin.cases L (Fin.cases κ (fun _ => j)), fun _ => κ⟩
  let φ : BinarySchema 3 := { body := es_value_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a U : φ.denote ρ a U ↔ Es_value_d I j κ L a U := es_value_sat_l I hZF.1 _ _ _ _ _ _
  obtain ⟨F, hf, hp⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := S) (target := Q) (fun a ha => by
      obtain ⟨n, _, hn⟩ := (hS a).mp ha
      obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF K n κ
      obtain ⟨U, hU⟩ := ed_filter_exists_l I hZF j a D
      exact ⟨U, (sat a U).mpr ⟨n, D, fn0_of_function_l (ZF.modelsKP hZF) hn,
        fun s => (hD s).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩, hU⟩⟩)
    (fun a _ U V hU hV => es_value_unique_l I hZF.1 ((sat a U).mp hU) ((sat a V).mp hV))
    (fun a U ha hU => by
      obtain ⟨m, hm, hma⟩ := (hS a).mp ha
      obtain ⟨n, D, hna, hD, hU⟩ := (sat a U).mp hU
      have he := hna.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
      apply (hQ U).mpr
      intro s hs
      exact (hP s).mpr fun b hb => (hT b).mpr ⟨n, he.symm ▸ hm,
        fn0_function_l (ZF.modelsKP hZF) ((hD b).mp (((hU s).mp hs).1 b hb))⟩)
  exact ⟨F, hf.1, hf.2.1, fun a U => (hp a U).trans (and_congr_right fun _ => sat a U)⟩

/-- j(κ^n) 对目标中的全部对象给出正确函数空间，而非仅对 j 的像成立。 -/
theorem es_seed_l (hZF : M.Models ZF) {ω X C Y E j n κ k D D' L a}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X C Y E j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hjn : M.PairMember I n n j) (hjκ : M.PairMember I κ k j) (hjD : M.PairMember I D D' j)
    (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s) (hL : M.MemberSubset L k) (haY : M.mem a Y)
    (ha : Fn0_d n L a) : M.mem a D' := by
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest)
  have tr := spred_forall_delta_l I hZF hω h hX hY φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem _ _) (fn0_delta_l ..))
    ⟨Fin.cases D (Fin.cases κ (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases D' (Fin.cases k (fun _ => n)), fun _ => n⟩ (Fin.cases hjD (Fin.cases hjκ (fun _ => hjn)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1] at tr
  exact (tr.mp (fun s _ => hD s) a haY).mpr (ha.mono_target_l hL)

/-- 每个有限支撑分量都是其对应 κ^n 上的适当超滤。 -/
theorem es_family_ultra_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d I j κ L S F) {a U} (ha : M.PairMember I a U F) :
    ∃ n D, Fn0_d n L a ∧ (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧
      Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U ∧ Ed_complete_d κ D U := by
  have ht := v_transitive_l I hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨haS, n, D, hna, hD, hU⟩ := (hF.2.2 a U).mp ha
  obtain ⟨m, hm, hma⟩ := (hS a).mp haS
  have he := hna.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
  have hn : M.mem n ω := he.symm ▸ hm
  have hnκ := hc.ordinal.transitive ω hωκ n hn
  have hDn : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) D n κ := fun s =>
    (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩
  have hDX := ZF.v_function_space_mem_l I hZF hX hδ hc.source (hc.ordinal.transitive n hnκ) hDn
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL (hSY a haS) hna
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨V, hV, hv⟩ := ed_ultrafilter_l I hZF hω h ht hY hP (v_power_mem_l I hX hδ hDX hP) hjD haD
  exact ⟨n, D, hna, hD, hU, ed_filter_unique_l I hZF.1 hV hU ▸ hv,
    ed_complete_l I hZF hω h hY hX hδ hc hjD haD hU⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑测度族自身的共同纤维条件

条件只读取实际测度函数 F，不把派生它的嵌入作为完备性参数。
第 n 个前缀所对应的测度包含第 n 层，恰好等价于像层具有共同纤维。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Es_fiber_d (ω L F H f : M.Domain) : Prop := Fn0_d ω L f ∧ ∀ n, M.mem n ω →
  ∃ A a U, Rd_entry_d n A H ∧ Fn0_d n L a ∧ M.MemberSubset a f ∧ M.PairMember I a U F ∧ M.mem A U

def es_fiber_m {d} (ω L F H f : Term d) : Formula 1 d := .conj (fn0_m ω L f)
  (Formula.forallMem ω (.existsE (.existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 2) H.weaken.weaken.weaken.weaken) (.conj
      (fn0_m (.bound 3) L.weaken.weaken.weaken.weaken (.bound 1)) (.conj
        (Formula.subset (.bound 1) f.weaken.weaken.weaken.weaken) (.conj
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken.weaken) (.mem (.bound 2) .newest)))))))))
derive_free_closed es_fiber_m

theorem es_fiber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L F H f : Term d) :
    Formula.satisfies ρ (es_fiber_m (𝒞 := 𝒞) ω L F H f) ↔
      Es_fiber_d I (ω.eval ρ) (L.eval ρ) (F.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [es_fiber_m, Es_fiber_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, rd_entry0_sat_l hE,
    Formula.satisfies_subset_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  rfl

theorem es_fiber_iff_l (hKP : M.Models KP) {j ω κ L S F H f}
    (hS : Fseq_space_d (kp_pair_l hKP) ω L S) (hF : Es_family_d I j κ L S F) (hH : Ef_levels_d ω κ H) :
    Es_fiber_d I ω L F H f ↔ Ef_image_fiber_d I j ω L H f := by
  constructor
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun n hn => ?_⟩
    obtain ⟨A, a, U, hA, ha, haf, haU, hAU⟩ := h n hn
    obtain ⟨_, _, _, _, _, hU⟩ := (hF.2.2 a U).mp haU
    obtain ⟨_, A', hjA, haA⟩ := (hU A).mp hAU
    exact ⟨A, A', a, hA, hjA, haA, ha, haf⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun n hn => ?_⟩
    obtain ⟨A, A', a, hA, hjA, haA, ha, haf⟩ := h n hn
    obtain ⟨U, haU⟩ := (hF.2.1 a).mp ((hS a).mpr ⟨n, hn, fn0_function_l hKP ha⟩)
    obtain ⟨_, m, D, hm, hD, hU⟩ := (hF.2.2 a U).mp haU
    have he := ha.domain_eq_l hKP.1 hm
    exact ⟨A, a, U, hA, ha, haf, haU, (hU A).mpr
      ⟨fun s hs => (hD s).mpr (he ▸ hH.2 n A hA s hs), A', hjA, haA⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 派生测度的实际坐标投影

先证明临界点以下序数间的内部函数逐点固定，再构造 p(s)=s∘q。
其有界定义传到目标，给出 j(p)(a)=a∘q；全程允许内部非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_small_function_fixed_l (hZF : M.Models ZF) {ω δ X C Y E j κ k m n q}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hm : M.mem m κ) (hn : M.mem n κ) (hq : Fn0_d m n q) : M.PairMember I q q j := by
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hqX := v_relation_mem_l I hX hδ hc.source (F := q) (fun p hp => by
    obtain ⟨i, hi, r, hr, hp⟩ := hq.1 p hp
    exact ⟨i, hc.ordinal.transitive m hm i hi, r, hc.ordinal.transitive n hn r hr, hp⟩)
  obtain ⟨q', _, hjq⟩ := hj.2.2 q hqX
  have hq' := (spred_function_l I hZF hω h ht hY (hc.fixed m hm) (hc.fixed n hn) hjq).mp hq
  have eq := hq.ext_l hZF.1 hq' (fun i hi => by
    obtain ⟨r, hr, hir⟩ := hq.2.1 i hi
    exact ⟨r, hir, (spred_entry_l I hZF hω h ht hY
      (hc.fixed i (hc.ordinal.transitive m hm i hi)) (hc.fixed r (hc.ordinal.transitive n hn r hr)) hjq).mp hir⟩)
  exact eq.symm ▸ hjq

/-- 投影及其像均实际存在；像投影在任意目标支撑上执行同一坐标重排。 -/
theorem ed_reindex_l (hZF : M.Models ZF) {ω δ X C Y E j κ k m n q H D L a b}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hm : M.mem m κ) (hn : M.mem n κ) (hq : Fn0_d m n q)
    (hH : ∀ s, M.mem s H ↔ Fn0_d n κ s) (hD : ∀ t, M.mem t D ↔ Fn0_d m κ t)
    (hL : M.MemberSubset L k) (haY : M.mem a Y) (hbY : M.mem b Y) (ha : Fn0_d n L a)
    (hb : Cp0_d m n L q a b) : ∃ H' D' p p', M.PairMember I H H' j ∧ M.PairMember I D D' j ∧ Fn0_d H D p ∧
      (∀ s t, Rd_entry_d s t p ↔ M.mem s H ∧ Cp0_d m n κ q s t) ∧
      M.PairMember I p p' j ∧ Rd_entry_d a b p' := by
  have ht := v_transitive_l I hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hjq := ed_small_function_fixed_l I hZF hω hX hδ h hY hc hm hn hq
  obtain ⟨R, hRX, hR⟩ := v_relation_cover_l I hX hδ hc.source
  have bound {l s} (hl : M.mem l κ) (hs : Fn0_d l κ s) : M.mem s R :=
    hR s fun p hp => (hs.1 p hp).elim fun i hi => hi.2.elim fun r hr =>
      ⟨i, hc.ordinal.transitive l hl i hi.1, r, hr⟩
  have space {l T} (hl : M.mem l κ) (hT : ∀ s, M.mem s T ↔ Fn0_d l κ s) : M.mem T X := by
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF R
    exact ht P (v_power_mem_l I hX hδ hRX hP) T ((hP T).mpr fun s hs => bound hl ((hT s).mp hs))
  obtain ⟨H', _, hjH⟩ := hj.2.2 H (space hn hH)
  obtain ⟨D', _, hjD⟩ := hj.2.2 D (space hm hD)
  obtain ⟨p, hp, spec⟩ := cp0_projection_l (ZF.modelsKP hZF) hq hH hD
  have hpX := v_relation_mem_l I hX hδ hRX (F := p) (fun r hr => by
    obtain ⟨s, hs, t, ht, hr⟩ := hp.1 r hr
    exact ⟨s, bound hn ((hH s).mp hs), t, bound hm ((hD t).mp ht), hr⟩)
  obtain ⟨p', _, hjp⟩ := hj.2.2 p hpX
  let φ : Formula 1 7 := Formula.forallMem (.bound 2) (Formula.forallMem (.bound 2)
    (.iff (rd_entry0_m (.bound 1) .newest (.bound 2))
      (cp0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest)))
  have tr := spred_delta_l I hZF hω h ht hY φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (cp0_delta_l ..))))
    ⟨Fin.cases p (Fin.cases D (Fin.cases H (Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m)))))), fun _ => m⟩
    ⟨Fin.cases p' (Fin.cases D' (Fin.cases H' (Fin.cases q (Fin.cases k (Fin.cases n (fun _ => m)))))), fun _ => m⟩
    (Fin.cases hjp (Fin.cases hjD (Fin.cases hjH (Fin.cases hjq (Fin.cases hc.image (Fin.cases (hc.fixed n hn)
      (fun _ => hc.fixed m hm)))))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1, cp0_sat_l hZF.1] at tr
  have target := tr.mp (fun s hs t _ => (spec s t).trans ⟨And.right, fun h => ⟨hs, h⟩⟩)
  have haH := es_seed_l I hZF hω h ht hY (hc.fixed n hn) hc.image hjH hH hL haY ha
  have hbD := es_seed_l I hZF hω h ht hY (hc.fixed m hm) hc.image hjD hD hL hbY hb.1
  exact ⟨H', D', p, p', hjH, hjD, hp, spec, hjp, (target a haH b hbD).mpr (cp0_mono_l hL hb)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑测度函数自身的协调律

每个实际坐标函数 q:m→n 都有实际逆像集合。协调条件只量化函数图与测度成员资格，
其证明从强嵌入构造投影及逆像，不把协调性作为扩展器的额外假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Es_pull_d (m n κ q A Z : M.Domain) : Prop := ∀ s, M.mem s Z ↔
  Fn0_d n κ s ∧ ∃ t, M.mem t A ∧ Cp0_d m n κ q s t

def es_pull_m {d} (m n κ q A Z : Term d) : Formula 1 d := .forallE (.iff (.mem .newest Z.weaken)
  (.conj (fn0_m n.weaken κ.weaken .newest) (Formula.existsMem A.weaken
    (cp0_m m.weaken.weaken n.weaken.weaken κ.weaken.weaken q.weaken.weaken (.bound 1) .newest))))
derive_free_closed es_pull_m

theorem es_pull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (m n κ q A Z : Term d) :
    Formula.satisfies ρ (es_pull_m m n κ q A Z) ↔
      Es_pull_d (m.eval ρ) (n.eval ρ) (κ.eval ρ) (q.eval ρ) (A.eval ρ) (Z.eval ρ) := by
  simp only [es_pull_m, Es_pull_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_existsMem_iff,
    cp0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Es_reindex_d (κ L F m n q a b U V A : M.Domain) : Prop := Fn0_d m n q → Fn0_d n L a →
  Cp0_d m n L q a b → M.PairMember I a V F → M.PairMember I b U F →
  (∀ t, M.mem t A → Fn0_d m κ t) → ∃ Z, Es_pull_d m n κ q A Z ∧ (M.mem Z V ↔ M.mem A U)

def es_reindex_m {d} (κ L F m n q a b U V A : Term d) : Formula 1 d :=
  .imp (fn0_m m n q) (.imp (fn0_m n L a) (.imp (cp0_m m n L q a b)
    (.imp (Formula.orderedPairMem 𝒞 a V F) (.imp (Formula.orderedPairMem 𝒞 b U F)
      (.imp (Formula.forallMem A (fn0_m m.weaken κ.weaken .newest)) (.existsE
        (.conj (es_pull_m m.weaken n.weaken κ.weaken q.weaken A.weaken .newest)
          (.iff (.mem .newest V.weaken) (.mem A.weaken U.weaken)))))))))
derive_free_closed es_reindex_m

theorem es_reindex_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L F m n q a b U V A : Term d) :
    Formula.satisfies ρ (es_reindex_m (𝒞 := 𝒞) κ L F m n q a b U V A) ↔
      Es_reindex_d I (κ.eval ρ) (L.eval ρ) (F.eval ρ) (m.eval ρ) (n.eval ρ) (q.eval ρ)
        (a.eval ρ) (b.eval ρ) (U.eval ρ) (V.eval ρ) (A.eval ρ) := by
  simp only [es_reindex_m, Es_reindex_d, Formula.satisfies_imp_iff, fn0_sat_l hE, cp0_sat_l hE,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, es_pull_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  rfl

def Es_coherent_d (ω κ L F : M.Domain) : Prop := ∀ m n q a b U V A, M.mem m ω → M.mem n ω →
  Es_reindex_d I κ L F m n q a b U V A

def es_coherent_m {d} (ω κ L F : Term d) : Formula 1 d :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 7) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (.mem (.bound 6) ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
        (es_reindex_m (𝒞 := 𝒞) κ.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          L.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed es_coherent_m

theorem es_coherent_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L F : Term d) :
    Formula.satisfies ρ (es_coherent_m (𝒞 := 𝒞) ω κ L F) ↔
      Es_coherent_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [es_coherent_m, Es_coherent_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, es_reindex_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem es_coherent_l (hZF : M.Models ZF) {ω δ X C Y E j κ k L S F}
    (hω : M.IsOmega ω) (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d I ω X C Y E j) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k)
    (hL : M.MemberSubset L k) (hSY : M.MemberSubset S Y) (hF : Es_family_d I j κ L S F) :
    Es_coherent_d I ω κ L F := by
  intro m n q a b U V A hm hn hq ha hb haV hbU hA
  have ht := v_transitive_l I hX
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨haS, r, H, hr, hH, hV⟩ := (hF.2.2 a V).mp haV
  obtain ⟨hbS, s, D, hs, hD, hU⟩ := (hF.2.2 b U).mp hbU
  have er := hr.domain_eq_l hZF.1 ha
  have es := hs.domain_eq_l hZF.1 hb.1
  have hH : ∀ t, M.mem t H ↔ Fn0_d n κ t := fun t => er ▸ hH t
  have hD : ∀ t, M.mem t D ↔ Fn0_d m κ t := fun t => es ▸ hD t
  obtain ⟨H', D', p, p', hjH, hjD, hp, spec, hjp, hab⟩ := ed_reindex_l I hZF hω hX hδ h hY hc
    (hc.ordinal.transitive ω hωκ m hm) (hc.ordinal.transitive ω hωκ n hn) hq hH hD hL (hSY a haS) (hSY b hbS) ha hb
  have hAD : M.MemberSubset A D := fun t ht => (hD t).mpr (hA t ht)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨A', _, hjA⟩ := hj.2.2 A (ht P (v_power_mem_l I hX hδ (hj.input_mem_of_pairMember hjD) hP)
    A ((hP A).mpr hAD))
  obtain ⟨Z, hz, hUV⟩ := ed_projection_l I hZF hω h hX hδ hY hjD hjH hjp hp hab hAD hjA hU hV
  refine ⟨Z, fun s => (hz s).trans ?_, hUV⟩
  exact ⟨fun ⟨hs, t, ht, hp⟩ => ⟨(hH s).mp hs, t, ht, ((spec s t).mp hp).2⟩,
    fun ⟨hs, t, ht, hc⟩ => ⟨(hH s).mpr hs, t, ht, (spec s t).mpr ⟨(hH s).mpr hs, hc⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑测度的源内分量与初等交换图

把已经构造的有限支撑协调律限制到实际源子集代数，自动构造坐标投影、
两侧源内部超幂、常值嵌入及分量间初等映射。全部集合和函数图均实际生成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel FilterZF
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem es_source_push_l {ω c X R κ L F m n q a b U V D E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X)
    (hDX : M.mem D X) (hEX : M.mem E X) (hmω : M.mem m ω) (hnω : M.mem n ω)
    (hq : Fn0_d m n q) (ha : Fn0_d n L a) (hb : Cp0_d m n L q a b)
    (haV : M.PairMember I a V F) (hbU : M.PairMember I b U F) (hc : Es_coherent_d I ω κ L F)
    (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s)
    (hU : Maximal_d (ℳ := M) D U) (hV : Maximal_d (ℳ := M) E V) : ∃ P Q U' V' t,
      Source_d X D P ∧ Source_d X E Q ∧ Rel_ultra_d D P U' ∧ Rel_ultra_d E Q V' ∧
      (∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) ∧ (∀ A, M.mem A V' ↔ M.mem A Q ∧ M.mem A V) ∧ M.mem t X ∧
      (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧ Push_d D E P Q U' V' t := by
  obtain ⟨t, htX, ht, spec⟩ := sc_reindex_l hZF hω hX hm theory hmX hnX hκX hqX hEX hq hD hE
  obtain ⟨P, U', hP, hU', hu⟩ := sc_source_ultrafilter_l I hZF hω hX hm theory hDX (hU.source_l (ZF.modelsKP hZF) (ZF.exists_powerSet hZF D) X)
  obtain ⟨Q, V', hQ, hV', hv⟩ := sc_source_ultrafilter_l I hZF hω hX hm theory hEX (hV.source_l (ZF.modelsKP hZF) (ZF.exists_powerSet hZF E) X)
  refine ⟨P, Q, U', V', t, hP, hQ, hU', hV', hu, hv, htX, spec, ht, fun A hA => ?_⟩
  obtain ⟨B, hBX, hB⟩ := sc_pull_l I hZF hω hX hm theory hEX htX ((hP A).mp hA).1
  have hBQ := (hQ B).mpr ⟨hBX, fun v hv => ((hB v).mp hv).1⟩
  obtain ⟨Z, hZ, hz⟩ := hc m n q a b U V A hmω hnω hq ha hb haV hbU
    (fun r hr => (hD r).mp (((hP A).mp hA).2 r hr))
  have eq : Z = B := by
    apply hZF.1.eq_of_same_members Z B
    intro s
    rw [hZ s, hB s]
    constructor
    · rintro ⟨hs, r, hr, hsρ⟩
      exact ⟨(hE s).mpr hs, r, hr, (spec s r).mpr ⟨(hE s).mpr hs, hsρ⟩⟩
    · rintro ⟨hs, r, hr, hsr⟩
      exact ⟨(hE s).mp hs, r, hr, ((spec s r).mp hsr).2⟩
  have readU : M.mem A U' ↔ M.mem A U := (hu A).trans ⟨And.right, fun h => ⟨hA, h⟩⟩
  have readV : M.mem B V' ↔ M.mem B V := (hv B).trans ⟨And.right, fun h => ⟨hBQ, h⟩⟩
  exact ⟨B, hBQ, hB, readV.trans ((eq ▸ hz).trans readU.symm)⟩

/-- 从真实有限支撑分量一次构造两侧超幂与三个初等映射，并给出交换方程。 -/
theorem es_source_projection_l {ω c X R κ L F m n q a b U V D E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (u₀ : Sc_uniform_d I ω X R D) (u₁ : Sc_uniform_d I ω X R E)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X)
    (hDX : M.mem D X) (hEX : M.mem E X) (hmω : M.mem m ω) (hnω : M.mem n ω)
    (hq : Fn0_d m n q) (ha : Fn0_d n L a) (hb : Cp0_d m n L q a b)
    (haV : M.PairMember I a V F) (hbU : M.PairMember I b U F) (hc : Es_coherent_d I ω κ L F)
    (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s)
    (hU : Maximal_d (ℳ := M) D U) (hV : Maximal_d (ℳ := M) E V) :
    ∃ P Q U' V' t G₀ G₁ o₀ o₁ p₀ p₁ C₀ C₁ T₀ T₁ i₀ i₁ K j,
      Source_d X D P ∧ Source_d X E Q ∧ Rel_ultra_d D P U' ∧ Rel_ultra_d E Q V' ∧
      (∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) ∧ (∀ A, M.mem A V' ↔ M.mem A Q ∧ M.mem A V) ∧
      M.mem t X ∧ Push_d D E P Q U' V' t ∧ (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧
      (∀ f, M.mem f G₀ ↔ M.mem f X ∧ Fn0_d D X f) ∧ (∀ f, M.mem f G₁ ↔ M.mem f X ∧ Fn0_d E X f) ∧
      Rp_model_d I D X U' R o₀ G₀ p₀ C₀ T₀ ∧ Rp_model_d I E X V' R o₁ G₁ p₁ C₁ T₁ ∧
      Smap_d I ω c o₀ X C₀ i₀ ∧ Smap_d I ω c o₁ X C₁ i₁ ∧ Smap_d I ω o₀ o₁ C₀ C₁ j ∧
      (∀ x B, M.PairMember I x B i₀ ↔ M.mem x X ∧ ∃ f, M.mem f G₀ ∧ Rs_const_d D x f ∧ M.PairMember I f B p₀) ∧
      (∀ x B, M.PairMember I x B i₁ ↔ M.mem x X ∧ ∃ f, M.mem f G₁ ∧ Rs_const_d E x f ∧ M.PairMember I f B p₁) ∧
      M.IsSetFunctionFromTo I K G₀ G₁ ∧
      (∀ f g, M.PairMember I f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d E D X t f g) ∧ Rp_lift_d I K p₀ p₁ j ∧
      ∀ x B A, M.PairMember I x B i₀ → (M.PairMember I B A j ↔ M.PairMember I x A i₁) := by
  obtain ⟨P, Q, U', V', t, hP, hQ, hU', hV', hu, hv, htX, coord, ht⟩ := es_source_push_l hZF hω hX hm theory
    hmX hnX hκX hqX hDX hEX hmω hnω hq ha hb haV hbU hc hD hE hU hV
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := sc_constant_l hZF hω hX hm theory hDX hDX
  obtain ⟨G₀, o₀, p₀, C₀, T₀, hG₀, hM₀⟩ := rp_family_model_l I hZF hU'.base hfX (hf.mono_target_l (hX A hAX)) R
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := sc_constant_l hZF hω hX hm theory hEX hDX
  obtain ⟨G₁, o₁, p₁, C₁, T₁, hG₁, hM₁⟩ := rp_family_model_l I hZF hV'.base hfX (hf.mono_target_l (hX A hAX)) R
  obtain ⟨K, j, hK, hk, hj, hl⟩ := rs_projection_embedding_l hZF hω hX hm theory u₀ u₁
    hDX hEX htX hP hQ hU' hV' ht hG₀ hG₁ hM₀ hM₁
  obtain ⟨i₀, hi₀, h₀⟩ := rs_constant_embedding_l hZF hω hX hm theory u₀ hDX hP hU' hG₀ hM₀
  obtain ⟨i₁, hi₁, h₁⟩ := rs_constant_embedding_l hZF hω hX hm theory u₁ hEX hQ hV' hG₁ hM₁
  exact ⟨P, Q, U', V', t, G₀, G₁, o₀, o₁, p₀, p₁, C₀, C₁, T₀, T₁, i₀, i₁, K, j,
    hP, hQ, hU', hV', hu, hv, htX, ht, coord, hG₀, hG₁, hM₀, hM₁, hi₀, hi₁, hj, h₀, h₁, hK, hk, hl,
    rs_projection_constant_l I hM₀.map hM₁.map ht.1 hK (fun f g h => ((hk f g).mp h).2.2)
      hj.1.1 hl hi₁.1.1 h₀ h₁⟩

end
end YesMetaZFC.SetTheory.LargeCardinal

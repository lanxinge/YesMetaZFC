import YesMetaZFC.SetTheory.LargeCardinal.MeasureCompleteness
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.Filter.Countable

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

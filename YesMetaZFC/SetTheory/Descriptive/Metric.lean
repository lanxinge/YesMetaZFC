import YesMetaZFC.SetTheory.Descriptive.Distance

/-! # 内部前缀超度量及距离图

距离是模型内规范有理数对的实际函数图。对称性、零距离分离、超度量不等式和
闭球刻画均在同一表示下证明；不从外部实数或外部函数空间取得任何模型数据。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Dist_d.symm_l {ω D z o f g q : M.Domain} (h : Dist_d I ω D z o f g q) :
    Dist_d I ω D z o g f q := by
  obtain ⟨n, hn, hq⟩ := h
  refine ⟨n, ?_, hq⟩
  rcases hn with ⟨en, e⟩ | ⟨hn, ha, x, y, hx, hy, hxy⟩
  · exact Or.inl ⟨en, e.symm⟩
  · exact Or.inr ⟨hn, ha.symm_l, y, x, hy, hx, fun e => hxy e.symm⟩

theorem ds_dist_zero_l (hKP : M.Models KP) {ω X D z o f g q}
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hg : M.IsSetFunctionFromTo I g ω X)
    (h : Dist_d I ω D z o f g q) : I.Codes q z o ↔ f = g := by
  have hzo : o ≠ z := fun e => ho.elim fun a ha => hz a (e ▸ ha.2.predecessor_mem)
  obtain ⟨n, hs, hd⟩ := h
  constructor
  · intro hq
    rcases hd with ⟨en, _⟩ | ⟨_, p, _, _, hq'⟩
    · exact hs.elim And.right (fun h => (KP.mem_irrefl_d hKP ω (en ▸ h.1)).elim)
    · exact (hzo (I.injective hq' hq).1).elim
  · intro e
    have en : n = ω := hs.elim And.left (fun ⟨_, _, x, y, hx, hy, hxy⟩ =>
      (hxy (hg.1.2 n x y (e ▸ hx) hy)).elim)
    exact hd.elim And.right (fun h => (KP.mem_irrefl_d hKP ω (en ▸ h.1)).elim)

/-- d(f,h)≤max(d(f,g),d(g,h))，用全序上等价的两个比较之一表达。 -/
theorem ds_ultrametric_l (hZF : M.Models ZF) {ω X D z o f g h p q r} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hg : M.IsSetFunctionFromTo I g ω X) (hh : M.IsSetFunctionFromTo I h ω X)
    (hp : Dist_d I ω D z o f g p) (hq : Dist_d I ω D z o g h q)
    (hr : Dist_d I ω D z o f h r) : Qle_d I z o r p ∨ Qle_d I z o r q := by
  have hD := Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩
  have refl {n v} (h : Dyad_d I ω D z o n v) : Qle_d I z o v v :=
    (dyad_le_l I hZF hω hz ho hd h h).mpr (Or.inr (Or.inl rfl))
  obtain ⟨n, hs, hpn⟩ := hp
  obtain ⟨m, ht, hqm⟩ := hq
  rcases hs with ⟨_, e⟩ | ⟨hn, ha, hb⟩
  · subst g
    have e := ds_dist_unique_l I hZF hω hD hh hr ⟨m, ht, hqm⟩
    exact Or.inr (e.symm ▸ refl hqm)
  · rcases ht with ⟨_, e⟩ | ⟨hm, hc, he⟩
    · subst h
      have e := ds_dist_unique_l I hZF hω hD hg hr ⟨n, Or.inr ⟨hn, ha, hb⟩, hpn⟩
      exact Or.inl (e.symm ▸ refl hpn)
    · have left (hsub : M.MemberSubset n m) : Qle_d I z o r p :=
        (ds_dist_ball_l I hZF hω hz ho hd hh hn hr hpn).mpr
          (fun i x hi => (ha i x hi).trans (hc i x (hsub i hi)))
      have right (hsub : M.MemberSubset m n) : Qle_d I z o r q :=
        (ds_dist_ball_l I hZF hω hz ho hd hh hm hr hqm).mpr
          (fun i x hi => (ha i x (hsub i hi)).trans (hc i x hi))
      rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn m hm with e | hnm | hmn
      · exact Or.inl (left (fun i hi => (e i).mp hi))
      · exact Or.inl (left (((hω.isOrdinal hZF).mem hm).transitive n hnm))
      · exact Or.inr (right (((hω.isOrdinal hZF).mem hn).transitive m hmn))

/-- 实际构造 0、1、2、点对域、分数码域和全部距离组成的模型内函数图。 -/
theorem ds_metric_graph_l (hZF : M.Models ZF) {ω X B} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) : ∃ z o D P Q F,
    (∀ x, ¬ M.mem x z) ∧ M.IsOrdinalOne o ∧ M.SuccessorOf D o ∧
    M.IsCartesianProduct I P B B ∧ M.IsCartesianProduct I Q ω ω ∧
    M.IsSetFunctionFromTo I F P Q ∧ ∀ f g p q, I.Codes p f g →
      (M.PairMember I p q F ↔ M.mem f B ∧ M.mem g B ∧ Dist_d I ω D z o f g q) := by
  obtain ⟨z, o, D, hz, hzω, ho, hoω, hd, hdω⟩ := ds_digits_l hω
  have hD := (hω.isOrdinal hZF).mem hdω
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B B
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I ω ω
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push D).push z).push o
  let φ : BinarySchema 4 := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
      (dist_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest (.bound 2)))) }
  have hp p q : φ.denote ρ p q ↔ ∃ f g, I.Codes p f g ∧ Dist_d I ω D z o f g q := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, dist_sat_l I hZF.1]; rfl
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := Q)
    (by
      intro p hpP
      obtain ⟨f, hf, g, hg, hfg⟩ := (hP p).mp hpP
      obtain ⟨q, hq⟩ := ds_dist_exists_l I hZF hω hdω ((hB f).mp hf) ((hB g).mp hg)
      exact ⟨q, (hp p q).mpr ⟨f, g, hfg, hq⟩⟩)
    (by
      intro p hpP q r hq hr
      obtain ⟨f, g, hfg, hq⟩ := (hp p q).mp hq
      obtain ⟨f', g', hfg', hr⟩ := (hp p r).mp hr
      obtain ⟨rfl, rfl⟩ := I.injective hfg hfg'
      obtain ⟨u, _, v, hv, huv⟩ := (hP p).mp hpP
      obtain ⟨rfl, rfl⟩ := I.injective hfg huv
      exact ds_dist_unique_l I hZF hω hD ((hB g).mp hv) hq hr)
    (by
      intro p q _ hq
      obtain ⟨f, g, _, n, _, hq⟩ := (hp p q).mp hq
      exact (hQ q).mpr (hq.elim (fun h => ⟨z, hzω, o, hoω, h.2⟩)
        (fun ⟨_, v, hv, _, h⟩ => ⟨o, hoω, v, hv, h⟩)))
  refine ⟨z, o, D, P, Q, F, hz, ho, hd, hP, hQ, hF, fun f g p q hfg => ?_⟩
  rw [hf p q, hp p q]
  constructor
  · rintro ⟨hpP, u, v, huv, hq⟩
    obtain ⟨rfl, rfl⟩ := I.injective hfg huv
    obtain ⟨u, hu, v, hv, huv⟩ := (hP p).mp hpP
    obtain ⟨rfl, rfl⟩ := I.injective hfg huv
    exact ⟨hu, hv, hq⟩
  · rintro ⟨hfB, hgB, hq⟩
    exact ⟨(hP p).mpr ⟨f, hfB, g, hgB, hfg⟩, f, g, hfg, hq⟩

end YesMetaZFC.SetTheory.Descriptive

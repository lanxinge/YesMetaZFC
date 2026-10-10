import YesMetaZFC.SetTheory.Descriptive.Projective.Finite

/-! # 解析子空间上的相对 Suslin 定理

环境只要求解析，未加强为闭或 Borel。先把两个相对解析迹恢复为实际解析集，
再用分离码；输出仍是现有 Borel 码在子空间上的解释。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem an_inter_l (hZF : M.Models ZF) {ω A B J K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hk : An_d I ω A B J K) (hl : An_d I ω A B J L) :
    ∃ V, An_d I ω A B J V ∧ Tr_d K L V := by
  obtain ⟨o, ho, hoω⟩ := hB.1.exists_ordinalOne_mem
  obtain ⟨z, hz, _⟩ := hB.1.1.1
  obtain ⟨p, hp, hv⟩ := (pc_sigma_l I hoω hz).mp ((ps_one_l I hZF hB.1 hA ho).mpr hk)
  obtain ⟨q, hq, hw⟩ := (pc_sigma_l I hoω hz).mp ((ps_one_l I hZF hB.1 hA ho).mpr hl)
  obtain ⟨r, V, hr, hv', eqn⟩ := pc_binary_l I hZF hB hA ha hJ hp hq false
  refine ⟨V, (ps_one_l I hZF hB.1 hA ho).mp ((pc_sigma_l I hoω hz).mpr ⟨r, hr, hv'⟩), fun x => ?_⟩
  have e : M.mem x V ↔ M.mem x B ∧ (M.mem x K ∧ M.mem x L) := (eqn x).trans
    (and_congr_right fun _ => and_congr (pev_mem_l I hZF hB.1 hv).symm (pev_mem_l I hZF hB.1 hw).symm)
  exact e.trans ⟨And.right, fun h => ⟨((an_proj_l I).mp hk).elim (fun _ k => ((k.2 x).mp h.1).1), h⟩⟩

theorem anrel_analytic_l (hZF : M.Models ZF) {ω A B J X K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : An_d I ω A B J X) (hk : Anrel_d I ω A B J X K) : An_d I ω A B J K := by
  obtain ⟨L, hl, tr⟩ := hk
  obtain ⟨V, hv, tv⟩ := an_inter_l I hZF hB hA ha hJ hX hl
  exact tr_unique_l hZF.1 tv tr ▸ hv

theorem suslin_relative_l (hZF : M.Models ZF) {ω A B J X K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : An_d I ω A B J X) : Borel_d I ω A A X K ↔
      Anrel_d I ω A B J X K ∧ ∃ L, Cm_d X K L ∧ Anrel_d I ω A B J X L := by
  have subX : M.MemberSubset X B := ((an_proj_l I).mp hX).elim fun _ h => fun x hx => ((h.2 x).mp hx).1
  have to_rel {K} (hk : Borel_d I ω A A X K) : Anrel_d I ω A B J X K := by
    obtain ⟨c, hc, hk⟩ := hk
    obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
    exact ⟨C, borel_an_l I hZF hB hA ha hJ ⟨c, hc, hC⟩, fun x => (hk x).trans
      (and_congr_right fun hx => ((hC x).trans ⟨And.right, fun h => ⟨subX x hx, h⟩⟩).symm)⟩
  constructor
  · intro hk
    obtain ⟨L, hl, hb⟩ := borel_compl_l I hZF hB.1 hA hk
    exact ⟨to_rel hk, L, hl, to_rel hb⟩
  · rintro ⟨hk, L, hl, hr⟩
    obtain ⟨C, ⟨c, hc, hC⟩, sub, disj⟩ := an_separation_l I hZF hB hA ha hJ
      (anrel_analytic_l I hZF hB hA ha hJ hX hk) (anrel_analytic_l I hZF hB hA ha hJ hX hr)
      (fun x ⟨hx, hy⟩ => ((hl x).mp hy).2 hx)
    have subK : M.MemberSubset K X := hk.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
    refine ⟨c, hc, fun x => ⟨fun hx => ⟨subK x hx, ((hC x).mp (sub x hx)).2⟩, ?_⟩⟩
    rintro ⟨hx, hv⟩
    exact Classical.byContradiction (fun hn => disj x ⟨(hC x).mpr ⟨subX x hx, hv⟩, (hl x).mpr ⟨hx, hn⟩⟩)

/-- 同一相对集合的 Σ¹₁、Π¹₁ 两码直接产生该子空间上的 Borel 码。 -/
theorem prden_suslin_l (hZF : M.Models ZF) {ω A B J X K z o p q} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : An_d I ω A B J X) (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o)
    (hp : Pc_d I ω A o z p) (hq : Pc_d I ω A o o q)
    (hk : Prden_d I ω A B J X p K) (hk' : Prden_d I ω A B J X q K) : Borel_d I ω A A X K := by
  obtain ⟨C, hc, trC⟩ := hk
  obtain ⟨D, hd, trD⟩ := hk'
  have hc := (ps_one_l I hZF hB.1 hA ho).mp ((pc_sigma_l I hp.1 hz).mpr ⟨p, hp, hc⟩)
  obtain ⟨R, hr, compl⟩ := (pp_one_l I hZF hB.1 hA ho).mp ((pc_pi_l I hq.1 ho).mpr ⟨q, hq, hd⟩)
  obtain ⟨L, trL⟩ := tr_exists_l (ZF.modelsKP hZF) X R
  have subX : M.MemberSubset X B := ((an_proj_l I).mp hX).elim fun _ h => fun x hx => ((h.2 x).mp hx).1
  exact (suslin_relative_l I hZF hB hA ha hJ hX).mpr ⟨⟨C, hc, trC⟩, L,
    cm_symm_l (fun x hx => ((trL x).mp hx).1) (tr_compl_l subX compl trL trD), R, hr, trL⟩

end YesMetaZFC.SetTheory.Descriptive

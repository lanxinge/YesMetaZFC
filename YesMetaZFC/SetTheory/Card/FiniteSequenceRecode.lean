import YesMetaZFC.SetTheory.Card.FiniteSequenceLift
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax

/-! # 字母双射诱导有限序列的序同构

逐项复合构造实际集合双射，并证明它精确保留包含关系；内部有限长度不要求外部标准。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fseq_recode_d (f p q : M.Domain) : Prop := (∀ z, M.mem z q → ∃ i y, (I).Codes z i y) ∧
  ∀ i y, M.PairMember I i y q ↔ ∃ x, M.PairMember I i x p ∧ M.PairMember I x y f

def fseq_recode_m {d} (f p q : Term d) : Formula 1 d :=
  .conj (Formula.isRelation 𝒞 q) (Formula.isComposition 𝒞 q f p)
derive_free_closed fseq_recode_m

theorem fseq_recode_sat_l {d} (ρ : Env M d) (f p q : Term d) :
    Formula.satisfies ρ (fseq_recode_m (𝒞 := 𝒞) f p q) ↔ Fseq_recode_d I (f.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [fseq_recode_m, Fseq_recode_d, Formula.isComposition, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem Fseq_recode_d.unique_l (hE : Extensional M) {f p q r : M.Domain}
    (hq : Fseq_recode_d I f p q) (hr : Fseq_recode_d I f p r) : q = r := by
  have sub {q r} (hq : Fseq_recode_d I f p q) (hr : Fseq_recode_d I f p r) z (hz : M.mem z q) : M.mem z r := by
    obtain ⟨i, y, c⟩ := hq.1 z hz
    obtain ⟨v, cv, hv⟩ := (hr.2 i y).mpr ((hq.2 i y).mp ⟨z, c, hz⟩)
    exact I.unique cv c ▸ hv
  exact hE.eq_of_same_members q r fun z => ⟨sub hq hr z, sub hr hq z⟩

/-- 逐项复合同时适用于内部有限列及任意集合长度的列。 -/
theorem ZF.fseq_compose_l (hZF : M.Models ZF) {f X Y n p : M.Domain}
    (ff : M.IsSetFunctionFromTo I f X Y) (fp : M.IsSetFunctionFromTo I p n X) :
    ∃ q, M.IsSetFunctionFromTo I q n Y ∧ Fseq_recode_d I f p q := by
  obtain ⟨q, fq, graph⟩ := ZF.exists_compositionFunction hZF I fp ff
  exact ⟨q, fq, fq.1.1, fun i y => (graph i y).trans
    ⟨And.right, fun h => ⟨h.elim fun _ hx => fp.input_mem_of_pairMember hx.1, h⟩⟩⟩

theorem Fseq_recode_d.function_l (hZF : M.Models ZF) {f X Y n p q : M.Domain}
    (ff : M.IsSetFunctionFromTo I f X Y) (fp : M.IsSetFunctionFromTo I p n X)
    (h : Fseq_recode_d I f p q) : M.IsSetFunctionFromTo I q n Y := by
  obtain ⟨r, fr, hr⟩ := ZF.fseq_compose_l I hZF ff fp
  exact hr.unique_l I hZF.1 h ▸ fr

theorem Fseq_recode_d.mono_l {f p q r s : M.Domain} (pr : Fseq_recode_d I f p r)
    (qs : Fseq_recode_d I f q s) (sub : M.MemberSubset p q) : M.MemberSubset r s := by
  intro z hz
  obtain ⟨i, y, c⟩ := pr.1 z hz
  obtain ⟨x, ⟨v, cv, hv⟩, xy⟩ := (pr.2 i y).mp ⟨z, c, hz⟩
  obtain ⟨w, cw, hw⟩ := (qs.2 i y).mpr ⟨x, ⟨v, cv, sub v hv⟩, xy⟩
  exact I.unique cw c ▸ hw

theorem Fseq_recode_d.subset_l {f X Y n p q r s : M.Domain}
    (hf : M.IsSetInjectionFromTo I f X Y) (fp : M.IsSetFunctionFromTo I p n X)
    (pr : Fseq_recode_d I f p r) (qs : Fseq_recode_d I f q s) :
    M.MemberSubset p q ↔ M.MemberSubset r s := by
  constructor
  · exact pr.mono_l I qs
  · intro sub z hz
    obtain ⟨i, x, c⟩ := fp.1.1 z hz
    have ix : M.PairMember I i x p := ⟨z, c, hz⟩
    obtain ⟨y, _, xy⟩ := hf.1.2.2 x (fp.output_mem_of_pairMember ix)
    obtain ⟨v, cv, hv⟩ := (pr.2 i y).mpr ⟨x, ix, xy⟩
    obtain ⟨x', ix', x'y⟩ := (qs.2 i y).mp ⟨v, cv, sub v hv⟩
    have eq := hf.2 x' x y x'y xy; subst x'
    obtain ⟨w, cw, hw⟩ := ix'
    exact I.unique cw c ▸ hw

/-- 每个字母双射自动给出全部内部有限序列的实际双射和逐项复合图。 -/
theorem ZF.fseq_recode_l (hZF : M.Models ZF) {ω X Y A B f : M.Domain} (hw : M.IsOmega ω)
    (sa : Fseq_space_d I ω X A) (sb : Fseq_space_d I ω Y B) (hf : M.IsSetBijectionFromTo I f X Y) :
    ∃ F, M.IsSetBijectionFromTo I F A B ∧
      (∀ p q, M.PairMember I p q F ↔ M.mem p A ∧ Fseq_recode_d I f p q) ∧
      ∀ p q r s, M.PairMember I p r F → M.PairMember I q s F → (M.MemberSubset p q ↔ M.MemberSubset r s) := by
  let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
  let φ : BinarySchema 1 := { body := fseq_recode_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  have sat p q : φ.denote ρ p q ↔ Fseq_recode_d I f p q := fseq_recode_sat_l I ..
  have compose := fun {n p} (fp : M.IsSetFunctionFromTo I p n X) => ZF.fseq_compose_l I hZF hf.1.1 fp
  obtain ⟨F, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := A) (target := B) (by
      intro p hp
      obtain ⟨n, _, fp⟩ := (sa p).mp hp
      obtain ⟨q, _, pq⟩ := compose fp
      exact ⟨q, (sat p q).mpr pq⟩)
    (fun _ _ _ _ hq hr => ((sat ..).mp hq).unique_l I hZF.1 ((sat ..).mp hr)) (by
      intro p q hp pq
      obtain ⟨n, hn, fp⟩ := (sa p).mp hp
      obtain ⟨r, fr, pr⟩ := compose fp
      exact pr.unique_l I hZF.1 ((sat ..).mp pq) ▸ (sb r).mpr ⟨n, hn, fr⟩)
  have gr p q : M.PairMember I p q F ↔ M.mem p A ∧ Fseq_recode_d I f p q :=
    (graph p q).trans (and_congr_right fun _ => sat p q)
  have order p q r s (pr : M.PairMember I p r F) (qs : M.PairMember I q s F) :
      M.MemberSubset p q ↔ M.MemberSubset r s := by
    obtain ⟨n, _, fp⟩ := (sa p).mp ((gr p r).mp pr).1
    exact ((gr p r).mp pr).2.subset_l I hf.1 fp ((gr q s).mp qs).2
  refine ⟨F, ⟨⟨fn, fun p q r pr qr => ?_⟩, fun q hq => ?_⟩, gr, order⟩
  · exact hZF.1.eq_of_same_members p q fun z =>
      ⟨(order p q r r pr qr).mpr (fun _ h => h) z, (order q p r r qr pr).mpr (fun _ h => h) z⟩
  · obtain ⟨n, hn, fq⟩ := (sb q).mp hq
    obtain ⟨p, fp, lift⟩ := ZF.fseq_lift_l I hZF hw hf.2 hn fq
    have pq : Fseq_recode_d I f p q := ⟨fq.1.1, fun i y => ⟨fun iy => by
      obtain ⟨x, _, ix⟩ := fp.2.2 i (fq.input_mem_of_pairMember iy)
      exact ⟨x, ix, lift i x y ix iy⟩, fun ⟨x, ix, xy⟩ => by
      obtain ⟨z, _, iz⟩ := fq.2.2 i (fp.input_mem_of_pairMember ix)
      exact hf.1.1.1.2 x z y (lift i x z ix iz) xy ▸ iz⟩⟩
    exact ⟨p, (sa p).mpr ⟨n, hn, fp⟩, (gr p q).mpr ⟨(sa p).mpr ⟨n, hn, fp⟩, pq⟩⟩

end YesMetaZFC.SetTheory

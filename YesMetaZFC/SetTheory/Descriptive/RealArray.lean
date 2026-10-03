import YesMetaZFC.SetTheory.Descriptive.Reindex

/-! # 一个内部实数编码可数列实数

第 i 行的第 j 项读取自然数配对 J(i,j) 处的值。逐坐标实数配对与取行交换。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Row_d (J i w x : M.Domain) : Prop := M.IsSetRelation I x ∧ ∀ j v,
  M.PairMember I j v x ↔ ∃ k, Np_d I J i j k ∧ M.PairMember I k v w
def row_m {d} (J i w x : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 x) (.forallE (.forallE
  (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest x.weaken.weaken) (.existsE (.conj
    (np_m (𝒞 := 𝒞) J.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 2) .newest)
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) w.weaken.weaken.weaken))))))
derive_free_closed row_m
theorem row_sat_l {d} (ρ : Env M d) (J i w x : Term d) :
    Formula.satisfies ρ (row_m (𝒞 := 𝒞) J i w x) ↔ Row_d I (J.eval ρ) (i.eval ρ) (w.eval ρ) (x.eval ρ) := by
  simp only [row_m, Row_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_exists_iff, np_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem row_unique_l (hE : Extensional M) {J i w x y} (h : Row_d I J i w x) (k : Row_d I J i w y) : x = y :=
  h.1.eq_of_pairMember_iff hE k.1 (fun j v => (h.2 j v).trans (k.2 j v).symm)

theorem row_index_l (hZF : M.Models ZF) {ω J i} (hJ : Npair_d I ω J) (hi : M.mem i ω) :
    ∃ E, M.IsSetFunctionFromTo I E ω ω ∧ ∀ j k, M.PairMember I j k E ↔ Np_d I J i j k := by
  let ρ : Env M 2 := (⟨fun _ => J, fun _ => J⟩ : Env M 1).push i
  let φ : BinarySchema 2 := { body := np_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp j k : φ.denote ρ j k ↔ Np_d I J i j k := np_sat_l I _ _ _ _ _
  obtain ⟨E, he, eqn⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := ω)
    (fun j hj => (np_total_l I hJ hi hj).imp fun k h => (hp j k).mpr h.2)
    (fun _ _ _ _ h k => np_unique_l I hJ ((hp _ _).mp h) ((hp _ _).mp k))
    (fun _ _ _ h => (np_type_l I hJ ((hp _ _).mp h)).2.2)
  exact ⟨E, he, fun j k => ((eqn j k).trans (and_congr_right fun _ => hp j k)).trans
    ⟨And.right, fun h => ⟨(np_type_l I hJ h).2.1, h⟩⟩⟩

theorem row_exists_l (hZF : M.Models ZF) {ω J i w} (hJ : Npair_d I ω J) (hi : M.mem i ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) : ∃ x, M.IsSetFunctionFromTo I x ω ω ∧ Row_d I J i w x := by
  obtain ⟨E, he, eqn⟩ := row_index_l I hZF hJ hi
  obtain ⟨x, hx, hr⟩ := re_exists_l I hZF he hw
  exact ⟨x, hx, hr.1, fun j v => (hr.2 j v).trans (exists_congr fun k => and_congr_left fun _ => eqn j k)⟩

def Rmap_d (B J i f : M.Domain) : Prop := M.IsSetFunctionFromTo I f B B ∧ ∀ w x,
  M.PairMember I w x f ↔ M.mem w B ∧ Row_d I J i w x
def rmap_m {d} (B J i f : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 f B B)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (.conj (.mem (.bound 1) B.weaken.weaken) (row_m (𝒞 := 𝒞) J.weaken.weaken i.weaken.weaken (.bound 1) .newest)))))
derive_free_closed rmap_m
theorem rmap_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J i f : Term d) :
    Formula.satisfies ρ (rmap_m (𝒞 := 𝒞) B J i f) ↔ Rmap_d I (B.eval ρ) (J.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [rmap_m, Rmap_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, row_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rmap_unique_l (hE : Extensional M) {B J i f g} (h : Rmap_d I B J i f) (k : Rmap_d I B J i g) : f = g :=
  h.1.1.1.eq_of_pairMember_iff hE k.1.1.1 (fun x y => (h.2 x y).trans (k.2 x y).symm)

theorem rmap_exists_l (hZF : M.Models ZF) {ω A B J i} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hi : M.mem i ω) :
    ∃ f, Rmap_d I B J i f ∧ Cont_d I A B f := by
  obtain ⟨E, he, eqn⟩ := row_index_l I hZF hJ hi
  obtain ⟨f, hf⟩ := rg_exists_l I hZF hB he
  have eqv w x : Re_d I E w x ↔ Row_d I J i w x := and_congr_right fun _ =>
    forall_congr' fun j => forall_congr' fun v => iff_congr Iff.rfl (exists_congr fun k => and_congr_left fun _ => eqn j k)
  exact ⟨f, ⟨hf.1, fun w x => (hf.2 w x).trans (and_congr_right fun _ => eqv w x)⟩, rg_cont_l I hZF hB hA he hf⟩

/-- 取行与逐坐标配对交换，量词运算因此不需要额外的实数重括号。 -/
theorem row_pair_l {ω J i w v p x y z} (hJ : Npair_d I ω J)
    (hx : Row_d I J i w x) (hy : Row_d I J i v y) (hp : Rp_d I J w v p)
    (hz : Rp_d I J x y z) : Row_d I J i p z := by
  refine ⟨hz.1, fun j a => ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨b, c, hb, hc, hbc⟩ := (hz.2 j a).mp h
    obtain ⟨k, hk, hkb⟩ := (hx.2 j b).mp hb
    obtain ⟨l, hl, hlc⟩ := (hy.2 j c).mp hc
    exact ⟨k, hk, (hp.2 k a).mpr ⟨b, c, hkb, np_unique_l I hJ hl hk ▸ hlc, hbc⟩⟩
  · rintro ⟨k, hk, hka⟩
    obtain ⟨b, c, hb, hc, hbc⟩ := (hp.2 k a).mp hka
    exact (hz.2 j a).mpr ⟨b, c, (hx.2 j b).mpr ⟨k, hk, hb⟩, (hy.2 j c).mpr ⟨k, hk, hc⟩, hbc⟩

end YesMetaZFC.SetTheory.Descriptive

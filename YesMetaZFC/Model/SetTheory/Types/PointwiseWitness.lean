import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Relations.Constant
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax

/-! # 代表函数的逐点赋值

只在原程序的有限坐标界内读取代表，界外可存放定义域和求值点参数。
每个代表是源内函数码，求值沿原关系进行，赋值同步更新保留精确逐点对应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_assign_d (b D X R a f p : M.Domain) : Prop := ∀ i, M.mem i b → ∃ g x,
  M.PairMember I i g a ∧ Rf_fun_d I X R D g ∧ Rf_val_d I X R p x g ∧ M.PairMember I i x f

def pe_assign_m {d} (b D X R a f p : Term d) : Formula 1 d := Formula.forallMem b (.existsE (.existsE
  (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) a.weaken.weaken.weaken)
    (.conj (rf_fun_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 1))
      (.conj (rf_val_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken p.weaken.weaken.weaken .newest (.bound 1))
        (Formula.orderedPairMem 𝒞 (.bound 2) .newest f.weaken.weaken.weaken))))))
derive_free_closed pe_assign_m

theorem pe_assign_sat_l {d} (ρ : Env M d) (b D X R a f p : Term d) :
    Formula.satisfies ρ (pe_assign_m (𝒞 := 𝒞) b D X R a f p) ↔
      Pe_assign_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [pe_assign_m, Pe_assign_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, rf_fun_sat_l I,
    rf_val_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem Pe_assign_d.update_l {b D X R a f p i g x a' f'} (h : Pe_assign_d I b D X R a f p)
    (hg : Rf_fun_d I X R D g) (hx : Rf_val_d I X R p x g)
    (ha : Senv_update_d I a i g a') (hf : Senv_update_d I f i x f') : Pe_assign_d I b D X R a' f' p := by
  intro j hj
  by_cases he : j = i
  · exact ⟨g, x, (ha.2 j g).mpr (Or.inl ⟨he, rfl⟩), hg, hx, (hf.2 j x).mpr (Or.inl ⟨he, rfl⟩)⟩
  · obtain ⟨v, y, hv, hy, hp, hjy⟩ := h j hj
    exact ⟨v, y, (ha.2 j v).mpr (Or.inr ⟨he, hv⟩), hy, hp, (hf.2 j y).mpr (Or.inr ⟨he, hjy⟩)⟩

theorem Pe_assign_d.congr_left_l {b D X R a a' f p} (h : Pe_assign_d I b D X R a f p)
    (ha : Senv_agree_d I b a a') : Pe_assign_d I b D X R a' f p := by
  intro i hi
  obtain ⟨g, x, hg, hf, hp, hx⟩ := h i hi
  exact ⟨g, x, (ha i g hi).mp hg, hf, hp, hx⟩

def Pe_repr_d (b D X R a : M.Domain) : Prop := ∀ i g,
  M.mem i b → M.PairMember I i g a → Rf_fun_d I X R D g

def pe_repr_m {d} (b D X R a : Term d) : Formula 1 d := Formula.forallMem b (.forallE
  (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest a.weaken.weaken)
    (rf_fun_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken D.weaken.weaken .newest)))
derive_free_closed pe_repr_m

theorem pe_repr_sat_l {d} (ρ : Env M d) (b D X R a : Term d) :
    Formula.satisfies ρ (pe_repr_m (𝒞 := 𝒞) b D X R a) ↔ Pe_repr_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) := by
  simp only [pe_repr_m, Pe_repr_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, rf_fun_sat_l I, Definitional.Term.eval_weaken]
  exact ⟨fun h i g hi => h i hi g, fun h i hi g => h i g hi⟩

def Pe_sat_d (b D X R E F n r a p : M.Domain) : Prop := ∃ f,
  M.mem f E ∧ Pe_assign_d I b D X R a f p ∧ Ssat_d I X R E F n r f

def pe_sat_m {d} (b D X R E F n r a p : Term d) : Formula 1 d := Formula.existsMem E
  (.conj (pe_assign_m (𝒞 := 𝒞) b.weaken D.weaken X.weaken R.weaken a.weaken .newest p.weaken)
    (ssat_m (𝒞 := 𝒞) X.weaken R.weaken E.weaken F.weaken n.weaken r.weaken .newest))
derive_free_closed pe_sat_m

theorem pe_sat_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b D X R E F n r a p : Term d) :
    Formula.satisfies ρ (pe_sat_m (𝒞 := 𝒞) b D X R E F n r a p) ↔
      Pe_sat_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ)
        (n.eval ρ) (r.eval ρ) (a.eval ρ) (p.eval ρ) := by
  simp only [pe_sat_m, Pe_sat_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pe_assign_sat_l I, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 原子翻译用图中有序对的成员作有界见证，不量化整个源载体。 -/
def pe_atom_m {d} (e : Bool) (p F G : Term d) : Formula 1 d :=
  Formula.existsMem F (Formula.existsMem .newest (Formula.existsMem .newest
    (.conj (rd_entry0_m p.weaken.weaken.weaken .newest F.weaken.weaken.weaken)
      (Formula.existsMem G.weaken.weaken.weaken (Formula.existsMem .newest (Formula.existsMem .newest
        (.conj (rd_entry0_m p.weaken.weaken.weaken.weaken.weaken.weaken .newest G.weaken.weaken.weaken.weaken.weaken.weaken)
          (if e then Formula.extensionalEq (.bound 3) .newest else .mem (.bound 3) .newest))))))))

@[simp] theorem pe_atom_closed_l {d} (e : Bool) (p F G : Term d)
    (hp : p.freeSupport = []) (hF : F.freeSupport = []) (hG : G.freeSupport = []) :
    (pe_atom_m e p F G).FreeClosed := by
  cases e <;> simp -implicitDefEqProofs [pe_atom_m, Definitional.Formula.FreeClosed, hp, hF, hG]

theorem pe_atom_sat_l (hE : Extensional M) {d} (ρ : Env M d) (e : Bool) (p F G : Term d) :
    Formula.satisfies ρ (pe_atom_m e p F G) ↔ ∃ x y,
      Rd_entry_d (p.eval ρ) x (F.eval ρ) ∧ Rd_entry_d (p.eval ρ) y (G.eval ρ) ∧
        if e then x = y else M.mem x y := by
  have bound {p x F : M.Domain} (h : Rd_entry_d p x F) : ∃ a b, M.mem a F ∧ M.mem b a ∧ M.mem x b := by
    obtain ⟨a, ⟨s, t, _, ht, ha⟩, hF⟩ := h
    exact ⟨a, t, hF, (ha t).mpr (Or.inr rfl), (ht x).mpr (Or.inr rfl)⟩
  have read : Formula.satisfies ρ (pe_atom_m e p F G) ↔ ∃ a b x, M.mem a (F.eval ρ) ∧ M.mem b a ∧ M.mem x b ∧
      Rd_entry_d (p.eval ρ) x (F.eval ρ) ∧ ∃ c d y, M.mem c (G.eval ρ) ∧ M.mem d c ∧ M.mem y d ∧
        Rd_entry_d (p.eval ρ) y (G.eval ρ) ∧ if e then x = y else M.mem x y := by
    cases e <;> simp only [pe_atom_m, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_existsMem_iff,
      Formula.satisfies_conj_iff, rd_entry0_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE,
      Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] <;> exact
        ⟨fun ⟨a, ha, b, hb, x, hx, hp, c, hc, d, hd, y, hy, hq, h⟩ => ⟨a, b, x, ha, hb, hx, hp, c, d, y, hc, hd, hy, hq, h⟩,
          fun ⟨a, b, x, ha, hb, hx, hp, c, d, y, hc, hd, hy, hq, h⟩ => ⟨a, ha, b, hb, x, hx, hp, c, hc, d, hd, y, hy, hq, h⟩⟩
  refine read.trans ⟨fun ⟨_, _, x, _, _, _, hx, _, _, y, _, _, _, hy, h⟩ => ⟨x, y, hx, hy, h⟩, ?_⟩
  rintro ⟨x, y, hx, hy, h⟩
  obtain ⟨a, b, ha, hb, hxb⟩ := bound hx
  obtain ⟨c, d, hc, hd, hyd⟩ := bound hy
  exact ⟨a, b, x, ha, hb, hxb, hx, c, d, y, hc, hd, hyd, hy, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 代表函数赋值的实际逐点求值

逐坐标读取源内函数码，支撑外取固定基点。唯一值收集构造完整内部赋值，
因此逐点解释的语义关系确有赋值见证，且无需选择原子值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_value_exists_l (hZF : M.Models ZF) {ω b D X R E a p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (ha : M.mem a E)
    (hb : M.MemberSubset b ω) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hh : ∀ i g, M.mem i b → M.PairMember I i g a → Rf_fun_d I X R D g) :
    ∃ f, M.mem f E ∧ Pe_assign_d I b D X R a f p := by
  classical
  let z := p
  have hz := hp
  let ρ : Env M 6 := ⟨Fin.cases b (Fin.cases p (Fin.cases a (Fin.cases z (Fin.cases X (fun _ => R))))), fun _ => z⟩
  let φ : BinarySchema 6 := {
    body := .disj
      (.conj (.mem (.bound 1) (.bound 2)) (.existsE (.conj
        (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 5)) (rf_val_m (𝒞 := 𝒞) (.bound 7) (.bound 8) (.bound 4) (.bound 1) .newest))))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 5))) }
  have sat i x : φ.denote ρ i x ↔
      (M.mem i b ∧ ∃ g, M.PairMember I i g a ∧ Rf_val_d I X R p x g) ∨ (¬ M.mem i b ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
      rf_val_sat_l I, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hA := (hE a).mp ha
  obtain ⟨f, hf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i _ => by
      by_cases hi : M.mem i b
      · obtain ⟨g, _, hg⟩ := hA.2.2 i (hb i hi)
        obtain ⟨x, hx⟩ := (hh i g hi hg).value_l I ext hp hd
        exact ⟨x, (sat i x).mpr (Or.inl ⟨hi, g, hg, hx⟩)⟩
      · exact ⟨z, (sat i z).mpr (Or.inr ⟨hi, rfl⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with ⟨hi, g, hg, hx⟩ | ⟨hi, rfl⟩ <;>
        rcases (sat i y).mp hy with ⟨hj, l, hl, hy⟩ | ⟨hj, rfl⟩
      · have eq := hA.1.2 i g l hg hl
        subst l
        exact (hh i g hi hg).unique_l I ext hx hy
      · exact (hj hi).elim
      · exact (hi hj).elim
      · rfl)
    (fun i x _ hx => by
      rcases (sat i x).mp hx with ⟨hi, g, hg, hx⟩ | ⟨_, rfl⟩
      · exact (hx.bounds_l I).2.1
      · exact hz)
  refine ⟨f, (hE f).mpr hf, fun i hi => ?_⟩
  obtain ⟨g, _, hg⟩ := hA.2.2 i (hb i hi)
  have hG := hh i g hi hg
  obtain ⟨x, hx⟩ := hG.value_l I ext hp hd
  exact ⟨g, x, hg, hG, hx, (spec i x).mpr ⟨hb i hi, (sat i x).mpr (Or.inl ⟨hi, g, hg, hx⟩)⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 逐点满足的赋值无关性与逻辑方程

代表函数在给定点的值唯一，故任意两份逐点赋值在整个支撑上相同。
随后直接读取原程序的 Tarski 方程；本层全部保持 ZF 强度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Pe_repr_d.update_l {b D X R a i g a'} (h : Pe_repr_d I b D X R a)
    (hg : Rf_fun_d I X R D g) (ha : Senv_update_d I a i g a') : Pe_repr_d I b D X R a' := by
  intro j f hj hf
  rcases (ha.2 j f).mp hf with ⟨_, rfl⟩ | ⟨_, hf⟩
  · exact hg
  · exact h j f hj hf

theorem Pe_assign_d.value_l {b D X R a f p i g x} (h : Pe_assign_d I b D X R a f p)
    (ext : Rf_ext_d I X R) (ha : M.IsSetFunction I a) (hf : M.IsSetFunction I f) (hi : M.mem i b) (hg : M.PairMember I i g a) :
    M.PairMember I i x f ↔ Rf_val_d I X R p x g := by
  obtain ⟨g', y, hg', hG, hy, hiy⟩ := h i hi
  have eq := ha.2 i g' g hg' hg
  subst g'
  exact ⟨fun hx => (hf.2 i x y hx hiy).symm ▸ hy,
    fun hx => (hG.unique_l I ext hx hy).symm ▸ hiy⟩

theorem Pe_assign_d.agree_right_l {b D X R a f g p} (h : Pe_assign_d I b D X R a f p)
    (k : Pe_assign_d I b D X R a g p) (ext : Rf_ext_d I X R) (ha : M.IsSetFunction I a)
    (hf : M.IsSetFunction I f) (hg : M.IsSetFunction I g) : Senv_agree_d I b f g := by
  intro i x hi
  obtain ⟨s, _, hs, _⟩ := h i hi
  exact (h.value_l I ext ha hf hi hs).trans (k.value_l I ext ha hg hi hs).symm

theorem pe_sat_value_l (hZF : M.Models ZF) {ω b D X R E F n r a p f}
    (ext : Rf_ext_d I X R) (hF : Sfm_d I ω n F) (hB : Sbound_d I F b) (hr : M.mem r n) (hE : M.IsFunctionSpace I E ω X)
    (ha : M.mem a E) (hf : M.mem f E) (he : Pe_assign_d I b D X R a f p) :
    Pe_sat_d I b D X R E F n r a p ↔ Ssat_d I X R E F n r f := by
  refine ⟨fun ⟨g, hg, hk, hs⟩ => ?_, fun hs => ⟨f, hf, he, hs⟩⟩
  exact (ssat_agree_l I hZF hF hB hE hr hg hf
    (hk.agree_right_l I he ext ((hE a).mp ha).1 ((hE g).mp hg).1 ((hE f).mp hf).1)).mp hs

theorem pe_sat_full_l (hZF : M.Models ZF) {ω b D X R E F n r a p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hB : Sbound_d I F b) (hb : M.MemberSubset b ω) (hr : M.mem r n)
    (ha : M.mem a E) (hh : Pe_repr_d I ω D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R) :
    Pe_sat_d I b D X R E F n r a p ↔ Pe_sat_d I ω D X R E F n r a p := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha (fun _ h => h) hp hd hh
  exact ⟨fun ht => ⟨f, hf, he, (pe_sat_value_l I hZF ext hF hB hr hE ha hf (fun i hi => he i (hb i hi))).mp ht⟩,
    fun ⟨g, hg, hk, ht⟩ => ⟨g, hg, fun i hi => hk i (hb i hi), ht⟩⟩

theorem pe_sat_atom_l (hZF : M.Models ZF) {ω b D X R E F n H r z i j a p g l x y}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hH : Seval_d I X R E F n H) (hB : Sbound_d I F b) (hb : M.MemberSubset b ω)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hc : M.PairMember I r z F) (e : Bool) (hs : Sop_d I (if e then 1 else 0) z i j)
    (hig : M.PairMember I i g a) (hjl : M.PairMember I j l a) (hx : Rf_val_d I X R p x g) (hy : Rf_val_d I X R p y l) :
    Pe_sat_d I b D X R E F n r a p ↔ if e then x = y else M.PairMember I x y R := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha hb hp hd hh
  have hix := (he.value_l I ext ((hE a).mp ha).1 ((hE f).mp hf).1 (hB.operands_l I hc hs).1 hig).mpr hx
  have hjy := (he.value_l I ext ((hE a).mp ha).1 ((hE f).mp hf).1 (hB.operands_l I hc hs).2 hjl).mpr hy
  apply (pe_sat_value_l I hZF ext hF hB ((hF.2.1.2.2 r).mpr ⟨z, hc⟩) hE ha hf he).trans
  cases e
  · exact ssat_rel_l I hZF hF hH hc hs hE hf hix hjy
  · exact ssat_eq_l I hZF hF hH hc hs hE hf hix hjy

theorem pe_sat_nor_l (hZF : M.Models ZF) {ω b D X R E F n H r z i j a p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hH : Seval_d I X R E F n H) (hB : Sbound_d I F b) (hb : M.MemberSubset b ω)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hc : M.PairMember I r z F) (hs : Sop_d I 2 z i j) (hi : M.mem i n) (hj : M.mem j n) :
    Pe_sat_d I b D X R E F n r a p ↔ ¬ (Pe_sat_d I b D X R E F n i a p ∨ Pe_sat_d I b D X R E F n j a p) := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha hb hp hd hh
  exact (pe_sat_value_l I hZF ext hF hB ((hF.2.1.2.2 r).mpr ⟨z, hc⟩) hE ha hf he).trans
    ((ssat_nor_l I hZF hF hH hc hs hf).trans (not_congr (or_congr
      (pe_sat_value_l I hZF ext hF hB hi hE ha hf he).symm (pe_sat_value_l I hZF ext hF hB hj hE ha hf he).symm)))

theorem pe_sat_ex_intro_l (hZF : M.Models ZF) {ω b D X R E F n H r z i j a a' g p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hH : Seval_d I X R E F n H) (hB : Sbound_d I F b) (hb : M.MemberSubset b ω)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hc : M.PairMember I r z F) (hs : Sop_d I 3 z i j) (hi : M.mem i ω) (hj : M.mem j n)
    (hg : Rf_fun_d I X R D g) (hu : Senv_update_d I a i g a') (ht : Pe_sat_d I b D X R E F n j a' p) :
    Pe_sat_d I b D X R E F n r a p := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha hb hp hd hh
  obtain ⟨x, hpx⟩ := hg.value_l I ext hp hd
  have hx := (hpx.bounds_l I).2.1
  obtain ⟨f', hff, hf'⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
  have body := (pe_sat_value_l I hZF ext hF hB hj hE
    ((hE a').mpr (hu.function_l I ((hE a).mp ha) hi (hg.mem_l I))) ((hE f').mpr hf') (he.update_l I hg hpx hu hff)).mp ht
  exact ⟨f, hf, he, (ssat_exists_l I hZF hF hH hc hs hf).mpr ⟨x, f', hx, hff, body⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内部函数族的对角与全定义域延拓

族 B 的定义域 A 可以只是 D 的子集。A 上读取 B(p)(p)，其余点取源中基点；
固定有界关系的源内统一化同时给出实际函数图和值域界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_diagonal_l {ω c X R D A B C} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hA : M.mem A X) (hB : M.mem B X) (hC : M.mem C X)
    (hAD : M.MemberSubset A D) (hBC : Fn0_d A C B)
    (hg : ∀ p g, Rd_entry_d p g B → Sfun_d X D g) :
    ∃ f, Sfun_d X D f ∧ ∀ p g x, Rd_entry_d p g B → (Rd_entry_d p x f ↔ Rd_entry_d p x g) := by
  classical
  obtain ⟨z, hz⟩ := hm.1.2.1
  let ρ : Env M 4 := ⟨Fin.cases A (Fin.cases B (Fin.cases C (fun _ => z))), fun _ => z⟩
  let φ : BinarySchema 4 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m (.bound 2) (.bound 1) .newest))))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 5))) }
  have sat p x : φ.denote ρ p x ↔ (M.mem p A ∧ ∃ g, M.mem g C ∧ Rd_entry_d p g B ∧ Rd_entry_d p x g) ∨
      (¬ M.mem p A ∧ x = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hd : φ.body.IsDelta0 := .disj (.conj (.mem _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    (.conj (.neg (.mem _ _)) (.atom _ _ _))
  obtain ⟨U, hUX, hu⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).union C hC
  obtain ⟨V, hVX, coords⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).envelope_l hUX
  obtain ⟨L, hL, hl⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).insert_l hVX hz
  have bound p g x (hgc : M.mem g C) (hpx : Rd_entry_d p x g) : M.mem x L := by
    obtain ⟨q, code, hqg⟩ := hpx
    exact (hl x).mpr (Or.inl (coords p x ⟨q, code, (hu q).mpr ⟨g, hgc, hqg⟩⟩).2)
  obtain ⟨f, hf, hFL, hs⟩ := sc_uniform_source_l hZF hω hX hm theory φ hd ρ
    (Fin.cases hA (Fin.cases hB (Fin.cases hC (fun _ => hz)))) hD hL (fun p hp => by
      by_cases ha : M.mem p A
      · obtain ⟨g, hgc, hpg⟩ := hBC.2.1 p ha
        obtain ⟨x, _, hpx⟩ := ((hg p g hpg).function_l hX).2.1 p hp
        exact ⟨x, bound p g x hgc hpx, (sat p x).mpr (Or.inl ⟨ha, g, hgc, hpg, hpx⟩)⟩
      · exact ⟨z, (hl z).mpr (Or.inr rfl), (sat p z).mpr (Or.inr ⟨ha, rfl⟩)⟩)
  have value p g x (hpg : Rd_entry_d p g B) (hpx : Rd_entry_d p x f) : Rd_entry_d p x g := by
    rcases (sat p x).mp (hs p x hpx) with ⟨_, g', _, hpg', hx⟩ | ⟨ha, _⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) hBC).1.2 p g' g hpg' hpg ▸ hx
    · exact (ha (hBC.bound_l hpg).1).elim
  refine ⟨f, ⟨hf, L, hL, hFL⟩, fun p g x hpg => ⟨value p g x hpg, fun hx => ?_⟩⟩
  obtain ⟨y, _, hy⟩ := hFL.2.1 p (hAD p (hBC.bound_l hpg).1)
  exact (fn0_function_l (ZF.modelsKP hZF) ((hg p g hpg).function_l hX)).1.2 p y x (value p g y hpg hy) hx ▸ hy

end YesMetaZFC.SetTheory.Internal

/-! ## 逐点编译的实际解释环境

编译程序与模型无关。解释存在量词只需源中的常值函数；这里把这一
已由源理论构造的性质写成原公式，供同时量化所有模型的内部归纳使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_context_d (ω c X R D E : M.Domain) : Prop := Rf_ext_d I X R ∧ Smdl_d I c X R ∧
  M.IsFunctionSpace I E ω X ∧ M.mem D X ∧
  ∀ x, M.mem x X → ∃ f, Rf_fun_d I X R D f ∧
    ∀ v, M.mem v X → M.PairMember I v D R → Rf_val_d I X R v x f

def pe_context_m {d} (ω c X R D E : Term d) : Formula 1 d :=
  .conj (rf_ext_m (𝒞 := 𝒞) X R) (.conj (smdl_m (𝒞 := 𝒞) c X R)
    (.conj (Formula.isFunctionSpace 𝒞 E ω X) (.conj (.mem D X)
      (Formula.forallMem X (.existsE (.conj
        (rf_fun_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken D.weaken.weaken .newest)
        (Formula.forallMem X.weaken.weaken (.imp
          (Formula.orderedPairMem 𝒞 .newest D.weaken.weaken.weaken R.weaken.weaken.weaken)
          (rf_val_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken .newest (.bound 2) (.bound 1))))))))))

@[simp] theorem pe_context_closed_l {d} (ω c X R D E : Term d)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hD : D.freeSupport = []) (hE : E.freeSupport = []) :
    (pe_context_m (𝒞 := 𝒞) ω c X R D E).FreeClosed := by
  simp -implicitDefEqProofs [pe_context_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hc, hX, hR, hD, hE]

theorem pe_context_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X R D E : Term d) :
    Formula.satisfies ρ (pe_context_m (𝒞 := 𝒞) ω c X R D E) ↔
      Pe_context_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) (D.eval ρ) (E.eval ρ) := by
  simp only [pe_context_m, Pe_context_d, Formula.satisfies_conj_iff, rf_ext_sat_l I hE,
    smdl_sat_l I, Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, rf_fun_sat_l I, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    rf_val_sat_l I, Definitional.Term.eval_weaken]; rfl

/-- 配对和乘积在当前原结构中直接构造常值图。 -/
theorem sc_pe_context_l {ω c Y S D E : M.Domain} (model : Smdl_d I c Y S)
    (ext : Rf_ext_d I Y S)
    (algebra : ∀ ρ : Env (smdl_structure_l I (R := S) model.2.1) 0, Formula.satisfies ρ sc_algebra_m)
    (hD : M.mem D Y) (hE : M.IsFunctionSpace I E ω Y) : Pe_context_d I ω c Y S D E := by
  have en := ext.native_l I model.2.1
  refine ⟨ext, model, hE, hD, fun x hx => ?_⟩
  let ρ : Env (smdl_structure_l I (R := S) model.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  obtain ⟨B, f, fn, val⟩ := sc_constant_raw_l en ρ (algebra ρ) ⟨D, hD⟩ ⟨x, hx⟩
  exact ⟨f.val, (rf_fun_native_l I model.2.1 en ⟨D, hD⟩ f).mpr ⟨B, fn⟩, fun v hv hd =>
    (rf_val_native_l I model.2.1 en ⟨v, hv⟩ ⟨x, hx⟩ f).mpr (val ⟨v, hv⟩ hd)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 逐点解释的内部行性质与翻译状态

b 同时界住原程序坐标并存放定义域参数，t 存放求值点。翻译状态中的实际
函数图把每条旧指令指向新程序的一行；全部语义条件都有可分离的原公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_row_d (b t D X R E F n m G r u : M.Domain) : Prop := ∀ p a f,
  M.PairMember I p D R → M.mem a E → M.mem f E → M.PairMember I b D a → M.PairMember I t p a →
    Pe_assign_d I b D X R a f p → (Ssat_d I X R E F n r f ↔ Ssat_d I X R E G m u a)

def pe_row_m {d} (b t D X R E F n m G r u : Term d) : Formula 1 d := .forallE
  (.imp (Formula.orderedPairMem 𝒞 .newest D.weaken R.weaken) (Formula.forallMem E.weaken (Formula.forallMem E.weaken.weaken
    (.imp (Formula.orderedPairMem 𝒞 b.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 1))
      (.imp (Formula.orderedPairMem 𝒞 t.weaken.weaken.weaken (.bound 2) (.bound 1))
        (.imp (pe_assign_m (𝒞 := 𝒞) b.weaken.weaken.weaken D.weaken.weaken.weaken X.weaken.weaken.weaken R.weaken.weaken.weaken
          (.bound 1) .newest (.bound 2))
          (.iff (ssat_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken E.weaken.weaken.weaken
            F.weaken.weaken.weaken n.weaken.weaken.weaken r.weaken.weaken.weaken .newest)
            (ssat_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken E.weaken.weaken.weaken
              G.weaken.weaken.weaken m.weaken.weaken.weaken u.weaken.weaken.weaken (.bound 1)))))))))
derive_free_closed pe_row_m

theorem pe_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b t D X R E F n m G r u : Term d) :
    Formula.satisfies ρ (pe_row_m (𝒞 := 𝒞) b t D X R E F n m G r u) ↔
      Pe_row_d I (b.eval ρ) (t.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ)
        (F.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (r.eval ρ) (u.eval ρ) := by
  simp only [pe_row_m, Pe_row_d, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, pe_assign_sat_l I, Formula.satisfies_iff_iff,
    ssat_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h p a f hp ha hf => h p hp a ha f hf, fun h p hp a ha f hf => h p a f hp ha hf⟩

def Pe_state_d (ω b t F n k m G T : M.Domain) : Prop := Sfm_d I ω m G ∧
  M.IsSetFunctionFromTo I T k m ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
    ∀ r u, M.PairMember I r u T → Pe_row_d I b t D X R E F n m G r u

def pe_state_m {d} (ω b t F n k m G T : Term d) : Formula 1 d :=
  let w (x : Term d) := x.weaken.weaken.weaken.weaken.weaken
  .conj (sfm_m (𝒞 := 𝒞) ω m G) (.conj (Formula.isFunctionFromTo 𝒞 T k m)
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
      (pe_context_m (𝒞 := 𝒞) (w ω) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (w T).weaken.weaken)
        (pe_row_m (𝒞 := 𝒞) (w b).weaken.weaken (w t).weaken.weaken (.bound 3) (.bound 5) (.bound 4)
          (.bound 2) (w F).weaken.weaken (w n).weaken.weaken (w m).weaken.weaken (w G).weaken.weaken
          (.bound 1) .newest)))))))))))
derive_free_closed pe_state_m

theorem pe_state_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b t F n k m G T : Term d) :
    Formula.satisfies ρ (pe_state_m (𝒞 := 𝒞) ω b t F n k m G T) ↔
      Pe_state_d I (ω.eval ρ) (b.eval ρ) (t.eval ρ) (F.eval ρ) (n.eval ρ)
        (k.eval ρ) (m.eval ρ) (G.eval ρ) (T.eval ρ) := by
  simp only [pe_state_m, Pe_state_d, Formula.satisfies_conj_iff, sfm_sat_l I hE,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, pe_context_sat_l I hE,
    pe_row_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem Pe_row_d.extend_l (hZF : M.Models ZF) {ω b t D X R E F n m G r u v J z}
    (h : Pe_row_d I b t D X R E F n m G r u) (hG : Sfm_d I ω m G)
    (hg : Sbuild_d I ω m G v J z) (hu : M.mem u m) : Pe_row_d I b t D X R E F n v J r u :=
  fun p a f hp ha hf hD ht he => (h p a f hp ha hf hD ht he).trans (hg.sat_l I hZF hG hu X R E a)

theorem pe_state_append_l (hZF : M.Models ZF) {ω b t F n k m G T l v J z}
    (hω : M.IsOmega ω) (hk : M.mem k ω) (hl : M.SuccessorOf l k) (h : Pe_state_d I ω b t F n k m G T)
    (hg : Sbuild_d I ω m G v J z) (hz : ∀ c X R D E, Pe_context_d I ω c X R D E → Pe_row_d I b t D X R E F n v J k z) :
    ∃ U, Pe_state_d I ω b t F n l v J U := by
  have hko := hω.members_areOrdinals (ZF.modelsKP hZF) k hk
  have seq : M.IsSequenceOfLength I T k := ⟨hko, h.2.1.1, h.2.1.2.1⟩
  obtain ⟨U, hU, he⟩ := seq.exists_append (ZF.modelsKP hZF) I (KP.successor_isOrdinal (ZF.modelsKP hZF) hko hl) hl (value := z)
  refine ⟨U, hg.program, ⟨hU.2.1, hU.2.2, fun i hi => ?_⟩, fun c X R D E context r u hu => ?_⟩
  · rcases (hl i).mp hi with hi | hi
    · obtain ⟨u, hu, hiu⟩ := h.2.1.2.2 i hi
      exact ⟨u, hg.span u hu, (he i u).mpr (Or.inl hiu)⟩
    · have eq := hZF.1.eq_of_same_members i k hi
      exact ⟨z, hg.root, (he i z).mpr (Or.inr ⟨eq, rfl⟩)⟩
  · rcases (he r u).mp hu with hu | ⟨rfl, rfl⟩
    · exact (h.2.2 c X R D E context r u hu).extend_l I hZF h.1 hg (h.2.1.output_mem_of_pairMember hu)
    · exact hz c X R D E context

end YesMetaZFC.SetTheory.Internal

/-! ## 逐点翻译的原子与布尔步骤

原子只读取两个代表函数在同一点的值；函数图的单值性给出精确语义。
或非复用已翻译的两行。这两步以及程序扩展均只需要 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_atom_step_l (hZF : M.Models ZF) {ω b t F n m G r z i j σ}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : Sbound_d I F b)
    (hG : Sfm_d I ω m G) (hc : M.PairMember I r z F)
    (e : Bool) (hs : Sop_d I (if e then 1 else 0) z i j)
    (hσ : M.mem σ ω) (ht : M.mem t σ) (hi : M.mem i σ) (hj : M.mem j σ) :
    ∃ v J k, Sbuild_d I ω m G v J k ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
      Pe_row_d I b t D X R E F n v J r k := by
  let q : Fin 3 → M.Domain := Fin.cases t (Fin.cases i (fun _ => j))
  let φ : Formula 1 3 := pe_atom_m e (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨v, J, k, h, read⟩ := sfm_template_l I hZF hω hG φ
    (pe_atom_closed_l e _ _ _ rfl rfl rfl) q hσ (Fin.cases ht (Fin.cases hi (fun _ => hj)))
  refine ⟨v, J, k, h, fun c X R D E context p a f hp ha hf _ htp he => ?_⟩
  obtain ⟨ext, model, hE, _, _⟩ := context
  let N := smdl_structure_l I (R := R) model.2.1
  have en := ext.native_l I model.2.1
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨g, x, hgi, hg, hpx, hix⟩ := he i (hb.operands_l I hc hs).1
  obtain ⟨l, y, hlj, hl, hpy, hjy⟩ := he j (hb.operands_l I hc hs).2
  let P : N.Domain := ⟨p, model.2.2.2 p D hp |>.1⟩
  let A : N.Domain := ⟨g, hg.mem_l I⟩
  let B : N.Domain := ⟨l, hl.mem_l I⟩
  let x' : N.Domain := ⟨x, hpx.bounds_l I |>.2.1⟩
  let y' : N.Domain := ⟨y, hpy.bounds_l I |>.2.1⟩
  let ρ : Env N 3 := ⟨Fin.cases P (Fin.cases A (fun _ => B)), fun _ => P⟩
  have new := (read X R model.2.1 E hE a ha ρ (Fin.cases htp (Fin.cases hgi (fun _ => hlj)))).trans
    (pe_atom_sat_l en ρ e (.bound 0) (.bound 1) (.bound 2))
  have value : (∃ u v : N.Domain, Rd_entry_d P u A ∧ Rd_entry_d P v B ∧
      if e then u = v else N.mem u v) ↔ if e then x = y else M.PairMember I x y R := by
    have eqv : (if e then x' = y' else N.mem x' y') ↔ if e then x = y else M.PairMember I x y R := by
      cases e
      · rfl
      · exact Subtype.ext_iff
    refine ⟨?_, fun hh => ⟨x', y', (rf_val_native_l I model.2.1 en P x' A).mp hpx,
      (rf_val_native_l I model.2.1 en P y' B).mp hpy, eqv.mpr hh⟩⟩
    rintro ⟨u, v, hu, hv, hh⟩
    have ex : u = x' := Subtype.ext (hg.unique_l I ext ((rf_val_native_l I model.2.1 en P u A).mpr hu) hpx)
    have ey : v = y' := Subtype.ext (hl.unique_l I ext ((rf_val_native_l I model.2.1 en P v B).mpr hv) hpy)
    exact eqv.mp (ex ▸ ey ▸ hh)
  have old : Ssat_d I X R E F n r f ↔ if e then x = y else M.PairMember I x y R := by
    cases e
    · exact ssat_rel_l I hZF hF hH hc hs hE hf hix hjy
    · exact ssat_eq_l I hZF hF hH hc hs hE hf hix hjy
  exact old.trans (new.trans value).symm

theorem pe_nor_step_l (hZF : M.Models ZF) {ω b t F n m G r c i j u v}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G)
    (hc : M.PairMember I r c F) (hs : Sop_d I 2 c i j) (hu : M.mem u m) (hv : M.mem v m) :
    ∃ l J k, Sbuild_d I ω m G l J k ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
      Pe_row_d I b t D X R E F n m G i u → Pe_row_d I b t D X R E F n m G j v →
      Pe_row_d I b t D X R E F n l J r k := by
  obtain ⟨l, J, k, h, read⟩ := sfm_nor_l I hZF hω hG hu hv
  refine ⟨l, J, k, h, fun c X R D E _ hi hj p a f hp ha hf hD ht he => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  exact (ssat_nor_l I hZF hF hH hc hs hf).trans ((not_congr
    (or_congr (hi p a f hp ha hf hD ht he) (hj p a f hp ha hf hD ht he))).trans (read X R E a ha).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 存在量词的逐点翻译

把对象见证改为定义域上的源内函数见证，并加入实际函数域代码。正向使用
源内常值函数，反向读取给定点处的值；两边均构造真实单坐标赋值更新。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pe_ex_step_l {ω F n b t m G r z i j v u σ}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G)
    (hc : M.PairMember I r z F) (hs : Sop_d I 3 z i j) (hv : M.mem v m) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hb : M.mem b σ) (hu : M.mem u σ)
    (hub : u ≠ b) (hui : u ≠ i) (hbi : b ≠ i) (hti : t ≠ i) :
    ∃ l J k, Sbuild_d I ω m G l J k ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
      Pe_row_d I b t D X R E F n m G j v → Pe_row_d I b t D X R E F n l J r k := by
  have hiω := hω.transitive (ZF.modelsKP hZF) σ hσ i hi
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_function_raw_l I hZF hω hG hσ hi hb hu hub hui
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨l, J, k, h₃, a₃⟩ := sfm_ex_l I hZF hω h₂.program hiω h₂.root
  refine ⟨l, J, k, (h₁.comp I h₂).comp I h₃, fun c X R D E context hj p a f hp ha hf hDa ht he => ?_⟩
  obtain ⟨ext, model, hE, hD, constants⟩ := context
  have en := ext.native_l I model.2.1
  have hpX := model.2.2.2 p D hp |>.1
  obtain ⟨V, hV⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  have body B a' (hB : M.mem B X) (ha' : Senv_update_d I a i B a') :
      Ssat_d I X R E F₂ n₂ r₂ a' ↔ Rf_fun_d I X R D B ∧ Ssat_d I X R E G m v a' := by
    have hA := (hE a').mpr (ha'.function_l I ((hE a).mp ha) hiω hB)
    rw [a₂ X R E a' hA, a₁ X R E c a' model ⟨B, hB⟩ ⟨D, hD⟩ en hE hA
      ((ha'.2 i B).mpr (Or.inl ⟨rfl, rfl⟩)) ((ha'.2 b D).mpr (Or.inr ⟨hbi, hDa⟩)),
      ← h₁.sat_l I hZF hG hv X R E a']
    exact and_congr (rf_fun_native_l I model.2.1 en ⟨D, hD⟩ ⟨B, hB⟩).symm Iff.rfl
  have row B x a' f' (hB : Rf_fun_d I X R D B) (hx : Rf_val_d I X R p x B)
      (ha' : Senv_update_d I a i B a') (hf' : Senv_update_d I f i x f') :
      Ssat_d I X R E F n j f' ↔ Ssat_d I X R E G m v a' :=
    hj p a' f' hp ((hE a').mpr (ha'.function_l I ((hE a).mp ha) hiω (hB.mem_l I)))
      ((hE f').mpr (hf'.function_l I ((hE f).mp hf) hiω (hx.bounds_l I).2.1))
      ((ha'.2 b D).mpr (Or.inr ⟨hbi, hDa⟩)) ((ha'.2 t p).mpr (Or.inr ⟨hti, ht⟩))
      (he.update_l I hB hx ha' hf')
  rw [ssat_exists_l I hZF hF hV hc hs hf, a₃ X R E a ha]
  constructor
  · rintro ⟨x, f', hx, hf', ht⟩
    obtain ⟨B, hfun, hB⟩ := constants x hx
    have hBX := hfun.mem_l I
    obtain ⟨a', ha', _⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hiω hBX
    exact ⟨B, a', hBX, ha', (body B a' hBX ha').mpr
      ⟨hfun, (row B x a' f' hfun (hB p hpX hp) ha' hf').mp ht⟩⟩
  · rintro ⟨B, a', hBX, ha', ht⟩
    obtain ⟨hB, hs⟩ := (body B a' hBX ha').mp ht
    obtain ⟨x, hpx⟩ := hB.value_l I ext hpX hp
    have hx := hpx.bounds_l I |>.2.1
    obtain ⟨f', hf', _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hiω hx
    exact ⟨x, f', hx, hf', (row B x a' f' hB hpx ha' hf').mpr hs⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部公式程序的逐点解释

对原程序的内部长度作原公式归纳。每个状态都包含实际新程序和旧根到新根的
函数图；后继步追加原子、或非或存在量词的翻译。归纳不要求内部 ω 标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pe_compile_bound_l {ω F n b t}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : M.mem b ω)
    (hB : Sbound_d I F b) (ht : M.SuccessorOf t b) :
    ∃ m G T, Pe_state_d I ω b t F n n m G T := by
  have htω : M.mem t ω := by
    obtain ⟨s, hs, hsω⟩ := hω.1.2 b hb
    exact (hZF.1.eq_of_same_members s t (fun i => (hs i).trans (ht i).symm)) ▸ hsω
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have bt : M.MemberSubset b t := fun i hi => (ht i).mpr (Or.inl hi)
  have tu : M.MemberSubset t u := fun i hi => (hu i).mpr (Or.inl hi)
  have uσ : M.MemberSubset u σ := fun i hi => (hσ i).mpr (Or.inl hi)
  have bσ : M.MemberSubset b σ := fun i hi => uσ i (tu i (bt i hi))
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  let ρ : Env M 5 := ⟨Fin.cases t (Fin.cases n (Fin.cases F (Fin.cases b (fun _ => ω)))), fun _ => ω⟩
  let φ : UnarySchema 5 := {
    body := .imp (Formula.subset .newest (.bound 2)) (.existsE (.existsE (.existsE
      (pe_state_m (𝒞 := kpair_convention_l) (.bound 8) (.bound 7) (.bound 4)
        (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have hφ k : φ.denote ρ k ↔ (M.MemberSubset k n → ∃ m G T, Pe_state_d I ω b t F n k m G T) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_exists_iff, pe_state_sat_l I hZF.1]; rfl
  have build : ∀ k, M.mem k ω → M.MemberSubset k n → ∃ m G T, Pe_state_d I ω b t F n k m G T := by
    apply hω.induction (fun k => M.MemberSubset k n → ∃ m G T, Pe_state_d I ω b t F n k m G T)
    · obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨A, fun k => (hA k).trans (and_congr_right fun _ => hφ k)⟩
    · intro e he _
      have seq := Structure.IsSequenceOfLength.empty I he
      have empty : ∀ i j, ¬ M.PairMember I i j e := fun _ _ ⟨p, _, hp⟩ => he p hp
      exact ⟨e, e, e, ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he), seq,
        fun i j h => (empty i j h).elim⟩, ⟨seq.2.1, seq.2.2, fun i hi => (he i hi).elim⟩,
        fun _ _ _ _ _ _ i j h => (empty i j h).elim⟩
    · intro k hk ih l hl hln
      have hkn := hln k hl.predecessor_mem
      obtain ⟨m, G, T, h⟩ := ih (fun i hi => hln i ((hl i).mpr (Or.inl hi)))
      obtain ⟨z, hz⟩ := (hF.2.1.2.2 k).mp hkn
      have step : ∃ v J r, Sbuild_d I ω m G v J r ∧ ∀ c X R D E, Pe_context_d I ω c X R D E → Pe_row_d I b t D X R E F n v J k r := by
        rcases hF.2.2 k z hz with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
          ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, _, hj⟩
        · obtain ⟨hi, hj⟩ := hB.operands_l I hz hs
          exact pe_atom_step_l I hZF hω hF hB h.1 hz false hs hσω
            (uσ t hu.predecessor_mem) (bσ i hi) (bσ j hj)
        · obtain ⟨hi, hj⟩ := hB.operands_l I hz hs
          exact pe_atom_step_l I hZF hω hF hB h.1 hz true hs hσω
            (uσ t hu.predecessor_mem) (bσ i hi) (bσ j hj)
        · obtain ⟨a, ha, hia⟩ := h.2.1.2.2 i hi
          obtain ⟨v, hv, hjv⟩ := h.2.1.2.2 j hj
          obtain ⟨v', J, r, build, read⟩ := pe_nor_step_l I hZF hω hF h.1 hz hs ha hv
          exact ⟨v', J, r, build, fun c X R D E context => read c X R D E context
            (h.2.2 c X R D E context i a hia) (h.2.2 c X R D E context j v hjv)⟩
        · have hi := (hB.operands_l I hz hs).1
          obtain ⟨v, hv, hjv⟩ := h.2.1.2.2 j hj
          obtain ⟨v', J, r, build, read⟩ := pe_ex_step_l hZF (b := b) (t := t) hω hF h.1 hz hs hv hσω (bσ i hi) (uσ b (tu b ht.predecessor_mem)) hσ.predecessor_mem
            (fun e => ir b (e ▸ tu b ht.predecessor_mem)) (fun e => ir i (e ▸ tu i (bt i hi)))
            (fun e => ir i (e ▸ hi)) (fun e => ir i (e ▸ bt i hi))
          exact ⟨v', J, r, build, fun c X R D E context => read c X R D E context
            (h.2.2 c X R D E context j v hjv)⟩
      obtain ⟨v, J, r, hg, hr⟩ := step
      obtain ⟨U, hU⟩ := pe_state_append_l I hZF hω hk hl h hg hr
      exact ⟨v, J, U, hU⟩
  exact build n hF.1 (fun _ h => h)

/-- 同一翻译程序适用于所有实际源环境，覆盖每一条内部指令。 -/
theorem pe_compile_l {ω F n} (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) :
    ∃ b t m G T, M.mem b ω ∧ Sbound_d I F b ∧ M.SuccessorOf t b ∧ M.mem t ω ∧
      Pe_state_d I ω b t F n n m G T := by
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hF
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  exact ⟨b, t, m, G, T, hb, hB, ht, htω, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源模型内的逐点真值集合

给定真实代表函数赋值，编译任意内部公式，再在源中分离其真值逆像。
逐点赋值由唯一值收集实际构造；参数赋值不必自身属于源模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一翻译程序的分离方程在任意实际源中读作逐点真值集合。 -/
theorem pe_separation_l {ω c X R D E F n r b t m G T k a aD A}
    (hω : M.IsOmega ω) (context : Pe_context_d I ω c X R D E)
    (hb : M.mem b ω) (ht : M.SuccessorOf t b) (h : Pe_state_d I ω b t F n n m G T)
    (hrk : M.PairMember I r k T) (ha : M.mem a E) (hh : Pe_repr_d I b D X R a)
    (hDa : Senv_update_d I a b D aD) :
    Sr_sep_d I X R E G m k t aD D A ↔
      ∀ p, M.mem p X → (M.PairMember I p A R ↔ M.PairMember I p D R ∧ Pe_sat_d I b D X R E F n r a p) := by
  have ext := context.1
  have model := context.2.1
  have hE := context.2.2.1
  have hD := context.2.2.2.1
  have haD := hDa.function_l I ((hE a).mp ha) hb hD
  have htω : M.mem t ω := by
    obtain ⟨s, hs, hsω⟩ := hω.1.2 b hb
    exact Structure.SuccessorOf.eq hZF.1 hs ht ▸ hsω
  have bt : M.MemberSubset b t := fun i hi => (ht i).mpr (Or.inl hi)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hbt : b ≠ t := fun e => ir t (e ▸ ht.predecessor_mem)
  have htb : ¬ M.mem t b := fun hi => ir t (bt t hi)
  have read p a' f (hp : M.PairMember I p D R) (hu : Senv_update_d I aD t p a')
      (hf : M.mem f E) (he : Pe_assign_d I b D X R a f p) :
      Ssat_d I X R E F n r f ↔ Ssat_d I X R E G m k a' := by
    have agree : Senv_agree_d I b a a' := fun i x hi =>
      (hDa.agree_l I (ir b) i x hi).trans (hu.agree_l I htb i x hi)
    exact h.2.2 c X R D E context r k hrk p a' f hp ((hE a').mpr (hu.function_l I haD htω (model.2.2.2 p D hp).1)) hf
      ((hu.2 b D).mpr (Or.inr ⟨hbt, (hDa.2 b D).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
      ((hu.2 t p).mpr (Or.inl ⟨rfl, rfl⟩)) (he.congr_left_l I agree)
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hpX
  apply iff_congr Iff.rfl
  apply and_congr_right
  intro hp
  constructor
  · rintro ⟨a', hu, hs⟩
    obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha (hω.transitive (ZF.modelsKP hZF) b hb) hpX hp hh
    exact ⟨f, hf, he, (read p a' f hp hu hf he).mpr hs⟩
  · rintro ⟨f, hf, he, hs⟩
    obtain ⟨a', hu, _⟩ := senv_update_exists_l I hZF haD htω (model.2.2.2 p D hp).1
    exact ⟨a', hu, (read p a' f hp hu hf he).mp hs⟩

/-- 传递隶属源的同一分离方程只在此处读作背景集合。 -/
theorem pe_separation_mem_l {ω c X R D E F n r b t m G T k a aD A}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (context : Pe_context_d I ω c X R D E) (hA : M.mem A X)
    (hb : M.mem b ω) (ht : M.SuccessorOf t b) (h : Pe_state_d I ω b t F n n m G T)
    (hrk : M.PairMember I r k T) (ha : M.mem a E) (hh : Pe_repr_d I b D X R a)
    (hDa : Senv_update_d I a b D aD) : Ssep_d I X R E G m k t aD D A ↔
      ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p := by
  have hD := context.2.2.2.1
  apply (ssep_relation_l I hX hm hD hA).symm.trans
  apply (pe_separation_l hZF hω context hb ht h hrk ha hh hDa).trans
  have mem p B (hp : M.mem p X) (hB : M.mem B X) : M.PairMember I p B R ↔ M.mem p B :=
    (hm.2 p B).trans ⟨fun h => h.2.2, fun h => ⟨hp, hB, h⟩⟩
  constructor
  · intro h p
    by_cases hp : M.mem p X
    · exact (mem p A hp hA).symm.trans ((h p hp).trans (and_congr (mem p D hp hD) Iff.rfl))
    · exact iff_of_false (fun h => hp (hX A hA p h)) (fun h => hp (hX D hD p h.1))
  · exact fun h p hp => (mem p A hp hA).trans ((h p).trans (and_congr (mem p D hp hD).symm Iff.rfl))

theorem sc_pe_trace_l {ω c X R D E F n r b a}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) :
    ∃ A, M.mem A X ∧ ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p := by
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨k, hk, hrk⟩ := h.2.1.2.2 r hr
  obtain ⟨aD, hDa, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hD
  obtain ⟨A, hAX, hA⟩ := theory.separation_l I hX hm E G m k t aD D hE h.1 hk htω ((hE aD).mpr haD) hD
  exact ⟨A, hAX, (pe_separation_mem_l hZF hω hX hm
    (sc_pe_context_l I hm.1 (rf_ext_mem_l I hZF.1 hX hm) (theory.algebra hm.1.2.1) hD hE) hAX
    hb ht h hrk ha hh hDa).mp hA⟩

/-- 任意内部程序、任意原关系函数码赋值的真值集，实际属于同一原始模型。 -/
theorem sc_pe_trace_raw_l {ω c Y S D E F n r b a}
    (hω : M.IsOmega ω) (context : Pe_context_d I ω c Y S D E) (theory : Sc_theory_d I ω Y S)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (hh : Pe_repr_d I b D Y S a) :
    ∃ A, M.mem A Y ∧ ∀ p, M.mem p Y →
      (M.PairMember I p A S ↔ M.PairMember I p D S ∧ Pe_sat_d I b D Y S E F n r a p) := by
  have hD := context.2.2.2.1
  have hE := context.2.2.1
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨k, hk, hrk⟩ := h.2.1.2.2 r hr
  obtain ⟨aD, hDa, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hD
  obtain ⟨A, hAY, sep⟩ := theory.separation E G m k t aD D hE h.1 hk htω ((hE aD).mpr haD) hD
  exact ⟨A, hAY, (pe_separation_l hZF hω context
    hb ht h hrk ha hh hDa).mp sep⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 存在行在源中具有统一代表见证

先在源内集合 A 上选取函数值见证，再取对角并延拓到整个 D。所得代表属于
源内部函数域，且在 A 的每一点满足原存在行的量词体；全部代码可以非标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_pe_witness_l {ω c X R D E F n V r z i j b a A}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) (hV : Seval_d I X R E F n V) (hc : M.PairMember I r z F)
    (hs : Sop_d I 3 z i j) (hj : M.mem j n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (hA : M.mem A X) (hAD : M.MemberSubset A D)
    (htot : ∀ p, M.mem p A → Pe_sat_d I b D X R E F n r a p) :
    ∃ g a', Sfun_d X D g ∧ Senv_update_d I a i g a' ∧ ∀ p, M.mem p A → Pe_sat_d I b D X R E F n j a' p := by
  have hi := (hB.operands_l I hc hs).1
  have hiω := hω.transitive (ZF.modelsKP hZF) b hb i hi
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have bt : M.MemberSubset b t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uσ : M.MemberSubset u σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hbi : b ≠ i := fun e => ir i (e ▸ hi)
  have hti : t ≠ i := fun e => ir i (e ▸ bt i hi)
  have hbt : b ≠ t := fun e => ir t (e ▸ ht.predecessor_mem)
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨v, hv, hjv⟩ := h.2.1.2.2 j hj
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_function_l I hZF hω h.1 hσω
    (uσ i (tu i (bt i hi))) (uσ b (tu b ht.predecessor_mem)) hσ.predecessor_mem
    (fun e => ir b (e ▸ tu b ht.predecessor_mem)) (fun e => ir i (e ▸ tu i (bt i hi)))
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨aD, hDa, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hD
  have agree p aT (hu : Senv_update_d I aD t p aT) : Senv_agree_d I b a aT := fun k x hk =>
    (hDa.agree_l I (ir b) k x hk).trans (hu.agree_l I (fun hi => ir t (bt t hi)) k x hk)
  have matrix p g aT aF (hp : M.mem p D) (hg : M.mem g X)
      (hT : Senv_update_d I aD t p aT) (hG : Senv_update_d I aT i g aF) :
      Ssat_d I X R E F₂ n₂ r₂ aF ↔ Sfun_d X D g ∧ Ssat_d I X R E G m v aF := by
    have haF := (hE aF).mpr (hG.function_l I (hT.function_l I haD htω (hX D hD p hp)) hiω hg)
    rw [a₂ X R E aF haF, a₁ X R E c aF g D hX hm hE haF
      ((hG.2 i g).mpr (Or.inl ⟨rfl, rfl⟩)) ((hG.2 b D).mpr (Or.inr ⟨hbi,
        (hT.2 b D).mpr (Or.inr ⟨hbt, (hDa.2 b D).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)),
      ← h₁.sat_l I hZF h.1 hv X R E aF]
  have row p g x aT aF f f' (hp : M.mem p D) (hg : Sfun_d X D g) (hx : Rd_entry_d p x g)
      (hT : Senv_update_d I aD t p aT) (hG : Senv_update_d I aT i g aF)
      (hf : M.mem f E) (he : Pe_assign_d I b D X R a f p) (hff : Senv_update_d I f i x f') :
      Ssat_d I X R E F n j f' ↔ Ssat_d I X R E G m v aF :=
    h.2.2 c X R D E (sc_pe_context_l I hm.1 (rf_ext_mem_l I hZF.1 hX hm) (theory.algebra hm.1.2.1) hD hE)
      j v hjv p aF f' ((hm.2 p D).mpr ⟨hX D hD p hp, hD, hp⟩) ((hE aF).mpr (hG.function_l I
      (hT.function_l I haD htω (hX D hD p hp)) hiω hg.1))
      ((hE f').mpr (hff.function_l I ((hE f).mp hf) hiω ((hg.function_l hX).bound_l hx).2))
      ((hG.2 b D).mpr (Or.inr ⟨hbi, (hT.2 b D).mpr
        (Or.inr ⟨hbt, (hDa.2 b D).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩))
      ((hG.2 t p).mpr (Or.inr ⟨hti, (hT.2 t p).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
      ((he.congr_left_l I (agree p aT hT)).update_l I ((rf_fun_mem_l I hZF.1 hX hm hD).mpr hg)
        ((rf_val_mem_l I hZF.1 hX hm hg.1).mpr hx) hG hff)
  obtain ⟨B, C, hBX, hCX, hBC, select⟩ := (sc_uniform_mem_l I hZF.1 hX hm hD).mp uniform E F₂ n₂ r₂ t i aD A hE h₂.program
    h₂.root htω hiω hti ((hE aD).mpr haD) hA hAD (fun p hp => by
      obtain ⟨f, hf, he, hsat⟩ := htot p hp
      obtain ⟨x, f', hx, hff, hsat⟩ := (ssat_exists_l I hZF hF hV hc hs hf).mp hsat
      obtain ⟨g, L, hg, hL, hfL, hcst⟩ := sc_constant_l hZF hω hX hm theory hD hx
      obtain ⟨aT, hT, haT⟩ := senv_update_exists_l I hZF haD htω (hX A hA p hp)
      obtain ⟨aF, hG, _⟩ := senv_update_exists_l I hZF haT hiω hg
      have hfun : Sfun_d X D g := ⟨hg, L, hL, hfL⟩
      exact ⟨g, hg, aT, aF, hT, hG, (matrix p g aT aF (hAD p hp) hg hT hG).mpr
        ⟨hfun, (row p g x aT aF f f' (hAD p hp) hfun ((hcst p x).mpr ⟨hAD p hp, rfl⟩) hT hG hf he hff).mp hsat⟩⟩)
  have chosen p g (hpg : Rd_entry_d p g B) : Sfun_d X D g := by
    obtain ⟨aT, aF, hT, hG, hs⟩ := select p g hpg
    exact ((matrix p g aT aF (hAD p (hBC.bound_l hpg).1) (hX C hCX g (hBC.bound_l hpg).2) hT hG).mp hs).1
  obtain ⟨g, hg, diag⟩ := sc_diagonal_l hZF hω hX hm theory hD hA hBX hCX hAD hBC chosen
  obtain ⟨a', ha', _⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hiω hg.1
  refine ⟨g, a', hg, ha', fun p hp => ?_⟩
  obtain ⟨f, hf, he, _⟩ := htot p hp
  obtain ⟨g', _, hpg⟩ := hBC.2.1 p hp
  obtain ⟨aT, aF, hT, hG, hs⟩ := select p g' hpg
  have hfun := chosen p g' hpg
  obtain ⟨x, hx, hpx⟩ := (hfun.function_l hX).2.1 p (hAD p hp)
  obtain ⟨f', hff, hf'⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hiω hx
  exact ⟨f', (hE f').mpr hf', he.update_l I ((rf_fun_mem_l I hZF.1 hX hm hD).mpr hg)
    ((rf_val_mem_l I hZF.1 hX hm hg.1).mpr ((diag p g' x hpg).mpr hpx)) ha' hff,
    (row p g' x aT aF f f' (hAD p hp) hfun hpx hT hG hf he hff).mpr
      ((matrix p g' aT aF (hAD p hp) hfun.1 hT hG).mp hs).2⟩

end YesMetaZFC.SetTheory.Internal

import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Relations.FunctionFamily
import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.Model.SetTheory.Relations.PointwiseWitness
import YesMetaZFC.SetTheory.Filter.Source
import YesMetaZFC.Model.SetTheory.Relations.FunctionCapture
import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 源内部代表赋值上的 Łoś 原公式

只在实际有限支撑 b 内要求函数代表及其商投影。满足关系读取已经定义的
逐点赋值，并由实际超滤成员承载；归纳不量化未经证明属于源的背景函数族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pe_holds_d (b D X R E F n r U a : M.Domain) : Prop := ∃ A, M.mem A U ∧
  ∀ p, M.mem p A → Pe_sat_d I b D X R E F n r a p

def pe_holds_m {d} (b D X R E F n r U a : Term d) : Formula 1 d := Formula.existsMem U
  (Formula.forallMem .newest (pe_sat_m (𝒞 := 𝒞) b.weaken.weaken D.weaken.weaken X.weaken.weaken
    R.weaken.weaken E.weaken.weaken F.weaken.weaken n.weaken.weaken r.weaken.weaken a.weaken.weaken .newest))
derive_free_closed pe_holds_m

theorem pe_holds_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b D X R E F n r U a : Term d) :
    Formula.satisfies ρ (pe_holds_m (𝒞 := 𝒞) b D X R E F n r U a) ↔
      Pe_holds_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ)
        (F.eval ρ) (n.eval ρ) (r.eval ρ) (U.eval ρ) (a.eval ρ) := by
  simp only [pe_holds_m, Pe_holds_d, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    pe_sat_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def Rs_eval_d (b D X R p a e : M.Domain) : Prop := ∀ i, M.mem i b → ∃ g B,
  M.PairMember I i g a ∧ Rf_fun_d I X R D g ∧ M.PairMember I g B p ∧ M.PairMember I i B e

def rs_eval_m {d} (b D X R p a e : Term d) : Formula 1 d := Formula.forallMem b (.existsE (.existsE
  (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) a.weaken.weaken.weaken)
    (.conj (rf_fun_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 1))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken.weaken)
        (Formula.orderedPairMem 𝒞 (.bound 2) .newest e.weaken.weaken.weaken))))))
derive_free_closed rs_eval_m

theorem rs_eval_sat_l {d} (ρ : Env M d) (b D X R p a e : Term d) :
    Formula.satisfies ρ (rs_eval_m (𝒞 := 𝒞) b D X R p a e) ↔
      Rs_eval_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (p.eval ρ) (a.eval ρ) (e.eval ρ) := by
  simp only [rs_eval_m, Rs_eval_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, rf_fun_sat_l I, Definitional.Term.eval_weaken]
  rfl

theorem Rs_eval_d.repr_l {b D X R p a e} (h : Rs_eval_d I b D X R p a e)
    (ha : M.IsSetFunction I a) : Pe_repr_d I b D X R a := by
  intro i g hi hg
  obtain ⟨g', _, hg', hG, _⟩ := h i hi
  exact ha.2 i g' g hg' hg ▸ hG

theorem Rs_eval_d.update_l {b D X R p a e i g B a' e'} (h : Rs_eval_d I b D X R p a e)
    (hg : Rf_fun_d I X R D g) (hp : M.PairMember I g B p) (ha : Senv_update_d I a i g a')
    (he : Senv_update_d I e i B e') : Rs_eval_d I b D X R p a' e' := by
  intro j hj
  by_cases eq : j = i
  · exact ⟨g, B, (ha.2 j g).mpr (Or.inl ⟨eq, rfl⟩), hg, hp, (he.2 j B).mpr (Or.inl ⟨eq, rfl⟩)⟩
  · obtain ⟨f, C, hf, hF, hp, hc⟩ := h j hj
    exact ⟨f, C, (ha.2 j f).mpr (Or.inr ⟨eq, hf⟩), hF, hp, (he.2 j C).mpr (Or.inr ⟨eq, hc⟩)⟩

def Rs_los_d (b D X R E F n U p C T K r : M.Domain) : Prop := ∀ a e,
  M.mem a E → M.mem e K → Rs_eval_d I b D X R p a e →
    (Pe_holds_d I b D X R E F n r U a ↔ Ssat_d I C T K F n r e)

def rs_los_m {d} (b D X R E F n U p C T K r : Term d) : Formula 1 d :=
  Formula.forallMem E (Formula.forallMem K.weaken
    (.imp (rs_eval_m (𝒞 := 𝒞) b.weaken.weaken D.weaken.weaken X.weaken.weaken R.weaken.weaken p.weaken.weaken (.bound 1) .newest)
      (.iff (pe_holds_m (𝒞 := 𝒞) b.weaken.weaken D.weaken.weaken X.weaken.weaken R.weaken.weaken
        E.weaken.weaken F.weaken.weaken n.weaken.weaken r.weaken.weaken U.weaken.weaken (.bound 1))
        (ssat_m (𝒞 := 𝒞) C.weaken.weaken T.weaken.weaken K.weaken.weaken F.weaken.weaken
          n.weaken.weaken r.weaken.weaken .newest))))
derive_free_closed rs_los_m

theorem rs_los_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b D X R E F n U p C T K r : Term d) :
    Formula.satisfies ρ (rs_los_m (𝒞 := 𝒞) b D X R E F n U p C T K r) ↔
      Rs_los_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ)
        (n.eval ρ) (U.eval ρ) (p.eval ρ) (C.eval ρ) (T.eval ρ) (K.eval ρ) (r.eval ρ) := by
  simp only [rs_los_m, Rs_los_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rs_eval_sat_l I, Formula.satisfies_iff_iff, pe_holds_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h a e ha he => h a ha e he, fun h a ha e he => h a e ha he⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源代表赋值的实际商投影

每个坐标已有一个源内代表，只需读取既有商投影。唯一值收集生成完整商赋值，
不在等价类中重新选择代表，也不要求背景的全部函数属于源。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rs_eval_exists_l (hZF : M.Models ZF) {ω D X R G p C E a}
    (hG : ∀ g, Rf_fun_d I X R D g → M.mem g G)
    (hp : M.IsSetFunctionFromTo I p G C) (hE : M.IsFunctionSpace I E ω X)
    (ha : M.mem a E) (hr : Pe_repr_d I ω D X R a) :
    ∃ e, M.IsSetFunctionFromTo I e ω C ∧ Rs_eval_d I ω D X R p a e := by
  let ρ : Env M 2 := ⟨Fin.cases a (fun _ => p), fun _ => a⟩
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 4))) }
  have sat i B : φ.denote ρ i B ↔ ∃ g, M.PairMember I i g a ∧ M.PairMember I g B p := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have hA := (hE a).mp ha
  obtain ⟨e, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := C)
    (fun i hi => by
      obtain ⟨g, _, hg⟩ := hA.2.2 i hi
      have hf := hr i g hi hg
      obtain ⟨B, _, hB⟩ := hp.2.2 g (hG g hf)
      exact ⟨B, (sat i B).mpr ⟨g, hg, hB⟩⟩)
    (fun i _ B C hB hC => by
      obtain ⟨g, hg, hBg⟩ := (sat i B).mp hB
      obtain ⟨f, hf, hCf⟩ := (sat i C).mp hC
      exact hp.1.2 g B C hBg (hA.1.2 i f g hf hg ▸ hCf))
    (fun i B _ hB => ((sat i B).mp hB).elim fun _ hg => hp.output_mem_of_pairMember hg.2)
  refine ⟨e, he, fun i hi => ?_⟩
  obtain ⟨B, _, hB⟩ := he.2.2 i hi
  obtain ⟨g, hg, hgp⟩ := (sat i B).mp ((spec i B).mp hB).2
  exact ⟨g, B, hg, hr i g hi hg, hgp, hB⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内真值逆像的超滤读取

只对实际容许的真值集合使用向上封闭与二择。逻辑或非由三个真值集合的
精确成员方程给出，不把背景中的任意真值逆像当作源中集合。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_holds_member_l {b D X R E F n r U a P A} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : M.mem A P) (hs : ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p) :
    M.mem A U ↔ Pe_holds_d I b D X R E F n r U a := by
  refine ⟨fun h => ⟨A, h, fun p hp => ((hs p).mp hp).2⟩, ?_⟩
  rintro ⟨B, hB, hb⟩
  exact hU.upward B A hB hA (fun p hp => (hs p).mpr ⟨hU.base.bounds B hB p hp, hb p hp⟩)

theorem pe_holds_nor_l {b D X R E F n r i j U a P A B C} (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U)
    (hA : M.mem A P) (hB : M.mem B P) (hC : M.mem C P)
    (hsA : ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n i a p)
    (hsB : ∀ p, M.mem p B ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n j a p)
    (hsC : ∀ p, M.mem p C ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p)
    (h : ∀ p, M.mem p D → (Pe_sat_d I b D X R E F n r a p ↔
      ¬ (Pe_sat_d I b D X R E F n i a p ∨ Pe_sat_d I b D X R E F n j a p))) :
    Pe_holds_d I b D X R E F n r U a ↔ ¬ (Pe_holds_d I b D X R E F n i U a ∨ Pe_holds_d I b D X R E F n j U a) := by
  have spec p : M.mem p C ↔ M.mem p D ∧ ¬ (M.mem p A ∨ M.mem p B) := by
    by_cases hp : M.mem p D
    · simpa only [hsC p, hsA p, hsB p, hp, true_and] using h p hp
    · simp only [hsC p, hp, false_and]
  exact (pe_holds_member_l I hU hC hsC).symm.trans ((hU.nor_l hA hB hC spec).trans
    (not_congr (or_congr (pe_holds_member_l I hU hA hsA) (pe_holds_member_l I hU hB hsB))))

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系函数码、实际坐标图与商赋值

每个坐标保留原模型的函数码及其实际图，再读取既有商投影。
全部条件都是背景模型内的公式，因而可对非标准长度的程序作内部行归纳。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rc_graph_d (X R t f g : M.Domain) : Prop := ∀ s x y, Rd_entry_d s x t →
  (Rd_entry_d s y g ↔ Rf_val_d I X R x y f)

def rc_graph_m {d} (X R t f g : Term d) : Formula 1 d := .forallE (.forallE (.forallE
  (.imp (rd_entry0_m (.bound 2) (.bound 1) t.weaken.weaken.weaken)
    (.iff (rd_entry0_m (.bound 2) .newest g.weaken.weaken.weaken)
      (rf_val_m (𝒞 := 𝒞) X.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 1) .newest f.weaken.weaken.weaken)))))
derive_free_closed rc_graph_m

theorem rc_graph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R t f g : Term d) :
    Formula.satisfies ρ (rc_graph_m (𝒞 := 𝒞) X R t f g) ↔
      Rc_graph_d I (X.eval ρ) (R.eval ρ) (t.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [rc_graph_m, Rc_graph_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hE, rf_val_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rc_graph_native_l {X R D t g} (nx : ∃ x, M.mem x X)
    (en : Extensional (smdl_structure_l I (R := R) nx))
    (ft : Fn0_d D X t) (fg : Fn0_d D X g) (f : (smdl_structure_l I (R := R) nx).Domain) :
    Rc_graph_d I X R t f.val g ↔ ∀ s (x y : (smdl_structure_l I (R := R) nx).Domain),
      Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  constructor
  · exact fun h s x y hsx => (h s x.val y.val hsx).trans (rf_val_native_l I nx en x y f)
  · intro h s x y hsx
    by_cases hy : M.mem y X
    · exact (h s ⟨x, (ft.bound_l hsx).2⟩ ⟨y, hy⟩ hsx).trans
        (rf_val_native_l I nx en ⟨x, (ft.bound_l hsx).2⟩ ⟨y, hy⟩ f).symm
    · exact iff_of_false (fun h => hy (fg.bound_l h).2) (fun h => hy (h.bounds_l I).2.1)

def Rc_eval_d (b d X R t p a e : M.Domain) : Prop := ∀ i, M.mem i b → ∃ f g B,
  M.PairMember I i f a ∧ Rf_fun_d I X R d f ∧ Rc_graph_d I X R t f g ∧
    M.PairMember I g B p ∧ M.PairMember I i B e

def rc_eval_m {k} (b d X R t p a e : Term k) : Formula 1 k := Formula.forallMem b
  (.existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 2) a.weaken.weaken.weaken.weaken)
    (.conj (rf_fun_m (𝒞 := 𝒞) X.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken d.weaken.weaken.weaken.weaken (.bound 2))
      (.conj (rc_graph_m (𝒞 := 𝒞) X.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken t.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
        (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken.weaken.weaken)
          (Formula.orderedPairMem 𝒞 (.bound 3) .newest e.weaken.weaken.weaken.weaken))))))))
derive_free_closed rc_eval_m

theorem rc_eval_sat_l (hE : Extensional M) {k} (ρ : Env M k) (b d X R t p a e : Term k) :
    Formula.satisfies ρ (rc_eval_m (𝒞 := 𝒞) b d X R t p a e) ↔
      Rc_eval_d I (b.eval ρ) (d.eval ρ) (X.eval ρ) (R.eval ρ) (t.eval ρ) (p.eval ρ) (a.eval ρ) (e.eval ρ) := by
  simp only [rc_eval_m, Rc_eval_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, rf_fun_sat_l I, rc_graph_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

theorem Rc_eval_d.repr_l {b d X R t p a e} (h : Rc_eval_d I b d X R t p a e)
    (ha : M.IsSetFunction I a) : Pe_repr_d I b d X R a := by
  intro i f hi hf
  obtain ⟨f', _, _, hf', fn, _⟩ := h i hi
  exact ha.2 i f' f hf' hf ▸ fn

theorem Rc_eval_d.update_l {b d X R t p a e i f g B a' e'} (h : Rc_eval_d I b d X R t p a e)
    (fn : Rf_fun_d I X R d f) (fg : Rc_graph_d I X R t f g) (gp : M.PairMember I g B p)
    (ha : Senv_update_d I a i f a') (he : Senv_update_d I e i B e') : Rc_eval_d I b d X R t p a' e' := by
  intro j hj
  by_cases eq : j = i
  · exact ⟨f, g, B, (ha.2 j f).mpr (Or.inl ⟨eq, rfl⟩), fn, fg, gp, (he.2 j B).mpr (Or.inl ⟨eq, rfl⟩)⟩
  · obtain ⟨f, g, B, hf, fn, fg, gp, hB⟩ := h j hj
    exact ⟨f, g, B, (ha.2 j f).mpr (Or.inr ⟨eq, hf⟩), fn, fg, gp, (he.2 j B).mpr (Or.inr ⟨eq, hB⟩)⟩

def Rc_holds_d (b d X R E F n r t U a : M.Domain) : Prop := ∃ A, M.mem A U ∧
  ∀ s x, M.mem s A → Rd_entry_d s x t → Pe_sat_d I b d X R E F n r a x

def rc_holds_m {k} (b d X R E F n r t U a : Term k) : Formula 1 k := Formula.existsMem U
  (Formula.forallMem .newest (.forallE (.imp (rd_entry0_m (.bound 1) .newest t.weaken.weaken.weaken)
    (pe_sat_m (𝒞 := 𝒞) b.weaken.weaken.weaken d.weaken.weaken.weaken X.weaken.weaken.weaken R.weaken.weaken.weaken
      E.weaken.weaken.weaken F.weaken.weaken.weaken n.weaken.weaken.weaken r.weaken.weaken.weaken a.weaken.weaken.weaken .newest))))
derive_free_closed rc_holds_m

theorem rc_holds_sat_l (hE : Extensional M) {k} (ρ : Env M k) (b d X R E F n r t U a : Term k) :
    Formula.satisfies ρ (rc_holds_m (𝒞 := 𝒞) b d X R E F n r t U a) ↔
      Rc_holds_d I (b.eval ρ) (d.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ)
        (n.eval ρ) (r.eval ρ) (t.eval ρ) (U.eval ρ) (a.eval ρ) := by
  simp only [rc_holds_m, Rc_holds_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, pe_sat_sat_l I hE, Definitional.Term.eval_weaken]
  exact exists_congr fun A => and_congr_right fun _ =>
    ⟨fun h s x hs => h s hs x, fun h s hs x => h s x hs⟩

def Rc_los_d (b d X R E F n t U p C T K r : M.Domain) : Prop := ∀ a e,
  M.mem a E → M.mem e K → Rc_eval_d I b d X R t p a e →
    (Rc_holds_d I b d X R E F n r t U a ↔ Ssat_d I C T K F n r e)

def rc_los_m {k} (b d X R E F n t U p C T K r : Term k) : Formula 1 k :=
  Formula.forallMem E (Formula.forallMem K.weaken
    (.imp (rc_eval_m (𝒞 := 𝒞) b.weaken.weaken d.weaken.weaken X.weaken.weaken R.weaken.weaken t.weaken.weaken p.weaken.weaken (.bound 1) .newest)
      (.iff (rc_holds_m (𝒞 := 𝒞) b.weaken.weaken d.weaken.weaken X.weaken.weaken R.weaken.weaken
        E.weaken.weaken F.weaken.weaken n.weaken.weaken r.weaken.weaken t.weaken.weaken U.weaken.weaken (.bound 1))
        (ssat_m (𝒞 := 𝒞) C.weaken.weaken T.weaken.weaken K.weaken.weaken F.weaken.weaken
          n.weaken.weaken r.weaken.weaken .newest))))
derive_free_closed rc_los_m

theorem rc_los_sat_l (hE : Extensional M) {k} (ρ : Env M k) (b d X R E F n t U p C T K r : Term k) :
    Formula.satisfies ρ (rc_los_m (𝒞 := 𝒞) b d X R E F n t U p C T K r) ↔
      Rc_los_d I (b.eval ρ) (d.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ)
        (n.eval ρ) (t.eval ρ) (U.eval ρ) (p.eval ρ) (C.eval ρ) (T.eval ρ) (K.eval ρ) (r.eval ρ) := by
  simp only [rc_los_m, Rc_los_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rc_eval_sat_l I hE, Formula.satisfies_iff_iff, rc_holds_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h a e ha he => h a ha e he, fun h a ha e he => h a e ha he⟩

theorem rc_holds_member_l {b d X R E F n r t U a D P A}
    (hU : FilterZF.Rel_ultra_d (ℳ := M) D P U) (hA : M.mem A P) (ft : Fn0_d D X t)
    (truth : ∀ s x, Rd_entry_d s x t → (M.mem s A ↔ Pe_sat_d I b d X R E F n r a x)) :
    M.mem A U ↔ Rc_holds_d I b d X R E F n r t U a := by
  refine ⟨fun h => ⟨A, h, fun s x hs hsx => (truth s x hsx).mp hs⟩, ?_⟩
  rintro ⟨B, hB, holds⟩
  apply hU.upward B A hB hA
  intro s hs
  obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds B hB s hs)
  exact (truth s x hsx).mpr (holds s x hs hsx)

end YesMetaZFC.SetTheory.Internal

/-! ## 原始关系源的完整内部 Łoś

归纳遍历全部内部程序行。布尔步只对原模型集合码的实际坐标逆像使用超滤二择；
存在步使用当前定义域上的统一化，取得同一函数码及其实际代表图。整个源无需坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_los_l {ω c' Y S D t P U o G p C T E K F n b r}
    (hω : M.IsOmega ω) (source : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (uniform : Sc_uniform_d I ω Y S d.val)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : FilterZF.Rel_ultra_d D P U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) (hE : M.IsFunctionSpace I E ω Y)
    (hK : M.IsFunctionSpace I K ω C) (hF : Sfm_d I ω n F)
    (hb : M.mem b ω) (hB : Sbound_d I F b) (hr : M.mem r n) :
    Rc_los_d I b d.val Y S E F n t U p C T K r := by
  have context := sc_pe_context_l I source ext (theory.algebra source.2.1) d.property hE
  have en := ext.native_l I source.2.1
  obtain ⟨V, hV⟩ := seval_exists_l I hZF Y S E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF C T K F hF.2.1.1
  let ρ : Env M 13 := ⟨Fin.cases K (Fin.cases T (Fin.cases C (Fin.cases p (Fin.cases U (Fin.cases t
    (Fin.cases n (Fin.cases F (Fin.cases E (Fin.cases S (Fin.cases Y (Fin.cases d.val (fun _ => b)))))))))))), fun _ => b⟩
  let φ : UnarySchema 13 := {
    body := rc_los_m (𝒞 := kpair_convention_l) (.bound 13) (.bound 12) (.bound 11)
      (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Rc_los_d I b d.val Y S E F n t U p C T K s := rc_los_sat_l I hZF.1 ..
  suffices h : φ.denote ρ r from (sat r).mp h
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (sat r).mpr
  intro a v ha hv eval
  have repr := eval.repr_l I ((hE a).mp ha).1
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  have trace s (hs : M.mem s n) : ∃ B A, M.mem B Y ∧
      (∀ x, M.mem x Y → (Rd_entry_d x B S ↔ Rd_entry_d x d.val S ∧ Pe_sat_d I b d.val Y S E F n s a x)) ∧
      M.mem A P ∧ ∀ w x, Rd_entry_d w x t → (M.mem w A ↔ Pe_sat_d I b d.val Y S E F n s a x) := by
    obtain ⟨B, hBY, truth⟩ := sc_pe_trace_raw_l hZF hω context theory hF hs hb hB ha repr
    obtain ⟨A, tr⟩ := rt_trace_exists_l I hZF D t S B
    exact ⟨B, A, hBY, truth, hP.pointwise_l I (fn0_function_l (ZF.modelsKP hZF) ft) domain hBY tr truth⟩
  obtain ⟨z, hz⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r z hz with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨fi, gi, B, hif, _, fgi, gip, hiB⟩ := eval i (hB.operands_l I hz hs).1
    obtain ⟨fj, gj, A, hjf, _, fgj, gjp, hjA⟩ := eval j (hB.operands_l I hz hs).2
    have fgi' := model.map.functions gi (model.map.projection.input_mem_of_pairMember gip)
    have fgj' := model.map.functions gj (model.map.projection.input_mem_of_pairMember gjp)
    have read s x y z (hsx : Rd_entry_d s x t) (hy : Rd_entry_d s y gi) (hz' : Rd_entry_d s z gj) :=
      pe_sat_atom_l I hZF ext hE hF hV hB bω ha repr (ft.bound_l hsx).2 (domain s x hsx) hz false hs hif hjf
        ((fgi s x y hsx).mp hy) ((fgj s x z hsx).mp hz')
    have atom : Rc_holds_d I b d.val Y S E F n r t U a ↔ Rp_rel_d I Y U S gi gj := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      constructor
      · intro holds s hsW
        obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨y, hy, hsy⟩ := fgi'.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨z, hz', hsz⟩ := fgj'.2.1 s (hU.base.bounds W hW s hsW)
        exact ⟨y, hy, z, hz', hsy, hsz, (read s x y z hsx hsy hsz).mp (holds s x hsW hsx)⟩
      · intro holds s x hsW hsx
        obtain ⟨y, _, z, _, hsy, hsz, hyz⟩ := holds s hsW
        exact (read s x y z hsx hsy hsz).mpr hyz
    exact atom.trans ((model.relation gi gj B A gip gjp).symm.trans (ssat_rel_l I hZF hF hJ hz hs hK hv hiB hjA).symm)
  · obtain ⟨fi, gi, B, hif, _, fgi, gip, hiB⟩ := eval i (hB.operands_l I hz hs).1
    obtain ⟨fj, gj, A, hjf, _, fgj, gjp, hjA⟩ := eval j (hB.operands_l I hz hs).2
    have fgi' := model.map.functions gi (model.map.projection.input_mem_of_pairMember gip)
    have fgj' := model.map.functions gj (model.map.projection.input_mem_of_pairMember gjp)
    have read s x y z (hsx : Rd_entry_d s x t) (hy : Rd_entry_d s y gi) (hz' : Rd_entry_d s z gj) :=
      pe_sat_atom_l I hZF ext hE hF hV hB bω ha repr (ft.bound_l hsx).2 (domain s x hsx) hz true hs hif hjf
        ((fgi s x y hsx).mp hy) ((fgj s x z hsx).mp hz')
    have atom : Rc_holds_d I b d.val Y S E F n r t U a ↔ Rp_eq_d Y U gi gj := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      constructor
      · intro holds s hsW
        obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨y, hy, hsy⟩ := fgi'.2.1 s (hU.base.bounds W hW s hsW)
        obtain ⟨z, _, hsz⟩ := fgj'.2.1 s (hU.base.bounds W hW s hsW)
        exact ⟨y, hy, hsy, ((read s x y z hsx hsy hsz).mp (holds s x hsW hsx)).symm ▸ hsz⟩
      · intro holds s x hsW hsx
        obtain ⟨y, _, hsy, hsz⟩ := holds s hsW
        exact (read s x y y hsx hsy hsz).mpr rfl
    exact atom.trans ((rp_kernel_l I hZF.1 hU.base model.map gip gjp).symm.trans (ssat_eq_l I hZF hF hJ hz hs hK hv hiB hjA).symm)
  · have hin := hF.2.1.1.transitive r hr i hi
    have hjn := hF.2.1.1.transitive r hr j hj
    obtain ⟨_, A, _, _, hA, pa⟩ := trace i hin
    obtain ⟨_, B, _, _, hB', pb⟩ := trace j hjn
    obtain ⟨_, W, _, _, hW, pw⟩ := trace r hr
    have spec s : M.mem s W ↔ M.mem s D ∧ ¬ (M.mem s A ∨ M.mem s B) := by
      by_cases hsD : M.mem s D
      · obtain ⟨x, hx, hsx⟩ := ft.2.1 s hsD
        exact (pw s x hsx).trans ((pe_sat_nor_l I hZF ext hE hF hV hB bω ha repr hx (domain s x hsx) hz hs hin hjn).trans
          ((not_congr (or_congr (pa s x hsx).symm (pb s x hsx).symm)).trans (and_iff_right hsD).symm))
      · exact iff_of_false (fun h => hsD (hU.field.bounds W hW s h)) (fun h => hsD h.1)
    have bool := (rc_holds_member_l I hU hW ft pw).symm.trans ((hU.nor_l hA hB' hW spec).trans
      (not_congr (or_congr (rc_holds_member_l I hU hA ft pa) (rc_holds_member_l I hU hB' ft pb))))
    exact bool.trans ((not_congr (or_congr ((sat i).mp (ih i hi) a v ha hv eval)
      ((sat j).mp (ih j hj) a v ha hv eval))).trans (ssat_nor_l I hZF hF hJ hz hs hv).symm)
  · have hjn := hF.2.1.1.transitive r hr j hj
    rw [ssat_exists_l I hZF hF hJ hz hs hv]
    constructor
    · rintro ⟨W, hW, holds⟩
      obtain ⟨B, _, hBY, truth, _, _⟩ := trace r hr
      obtain ⟨f, Q, fn, a', update, witness⟩ := sc_pe_witness_raw_l hZF hω source
        d ⟨B, hBY⟩ context uniform hF hz hs hjn hb hB ha (fun x _ hx => ((truth x.val x.property).mp hx).2)
      obtain ⟨g, fg, decode⟩ := smdl_function_l hZF source.2.1 (smdl_extensional_l hZF source ext) d Q f fn ft domain
      have hg := (hG g).mpr ⟨fg, Q, f, fn, decode⟩
      obtain ⟨B', hBC, gp⟩ := model.map.projection.2.2 g hg
      obtain ⟨v', uv, hv'⟩ := senv_update_exists_l I hZF ((hK v).mp hv) hi hBC
      have ff := (rf_fun_native_l I source.2.1 en d f).mpr ⟨Q, fn⟩
      have gr := (rc_graph_native_l I source.2.1 en ft fg f).mpr decode
      refine ⟨B', v', hBC, uv, ((sat j).mp (ih j hj) a' v'
        ((hE a').mpr (update.function_l I ((hE a).mp ha) hi f.property)) ((hK v').mpr hv')
        (eval.update_l I ff gr gp update uv)).mp ⟨W, hW, ?_⟩⟩
      intro s x hsW hsx
      exact witness ⟨x, (ft.bound_l hsx).2⟩ (domain s x hsx)
        ((truth x (ft.bound_l hsx).2).mpr ⟨domain s x hsx, holds s x hsW hsx⟩)
    · rintro ⟨B, v', hBC, uv, truth⟩
      obtain ⟨g, gp⟩ := (model.map.range B).mp hBC
      obtain ⟨fg, Q, f, fn, decode⟩ := (hG g).mp (model.map.projection.input_mem_of_pairMember gp)
      have ff := (rf_fun_native_l I source.2.1 en d f).mpr ⟨Q, fn⟩
      have gr := (rc_graph_native_l I source.2.1 en ft fg f).mpr decode
      obtain ⟨a', update, ha'⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hi f.property
      obtain ⟨W, hW, holds⟩ := ((sat j).mp (ih j hj) a' v' ((hE a').mpr ha')
        ((hK v').mpr (uv.function_l I ((hK v).mp hv) hi hBC)) (eval.update_l I ff gr gp update uv)).mpr truth
      exact ⟨W, hW, fun s x hsW hsx => pe_sat_ex_intro_l I hZF ext hE hF hV hB bω ha repr
        (ft.bound_l hsx).2 (domain s x hsx) hz hs hi hjn ff update (holds s x hsW hsx)⟩

/-- 同一代表赋值上全部内部公式码的统一满足关系。 -/
theorem rc_satisfies_l {ω c' Y S D t P U o G p C T E}
    (hω : M.IsOmega ω) (source : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (uniform : Sc_uniform_d I ω Y S d.val)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : FilterZF.Rel_ultra_d D P U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) (hE : M.IsFunctionSpace I E ω Y)
    {Z a v z} (codes : Scode_d I ω Z) (ha : M.mem a E) (hv : M.IsSetFunctionFromTo I v ω C)
    (eval : Rc_eval_d I ω d.val Y S t p a v) (hz : M.mem z Z) :
    Satisfies_d I ω o z v ↔ ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x t →
      ∃ f, M.mem f E ∧ Pe_assign_d I ω d.val Y S a f x ∧ Satisfies_d I ω c' z f := by
  obtain ⟨n, F, r, code⟩ := (codes z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  have repr := eval.repr_l I ((hE a).mp ha).1
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  have los := rc_los_l hZF hω source ext theory d uniform ft domain hP hU hG model
    hE hK code.2.1 hb bound code.2.2 a v ha ((hK v).mpr hv) (fun i hi => eval i (bω i hi))
  apply (satisfies_decode_l I hZF.1 model.code code hK).trans (los.symm.trans ?_)
  apply exists_congr
  intro A
  apply and_congr_right
  intro _
  apply forall_congr'
  intro s
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro hsx
  apply (pe_sat_full_l I hZF ext hE code.2.1 bound bω code.2.2 ha repr (ft.bound_l hsx).2 (domain s x hsx)).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 source code hE).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 源内部函数族的完整内部 Łoś 定理

在实际原公式 rs_los_m 上作内部行归纳。或非步使用源内真值逆像，存在步
调用已构造的源内统一代表；商始终只使用源中实际拥有的函数图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_los_l {ω c X R D P U o G p C T E K F n b r}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hP : FilterZF.Source_d X D P)
    (hU : FilterZF.Rel_ultra_d D P U) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hM : Rp_model_d I D X U R o G p C T) (hE : M.IsFunctionSpace I E ω X)
    (hK : M.IsFunctionSpace I K ω C) (hF : Sfm_d I ω n F)
    (hb : M.mem b ω) (hB : Sbound_d I F b) (hr : M.mem r n) : Rs_los_d I b D X R E F n U p C T K r := by
  have ext := rf_ext_mem_l I hZF.1 hX hm
  have point v (hv : M.mem v D) := (hm.2 v D).mpr ⟨hX D hD v hv, hD, hv⟩
  obtain ⟨V, hV⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF C T K F hF.2.1.1
  let ρ : Env M 12 := ⟨Fin.cases K (Fin.cases T (Fin.cases C (Fin.cases p (Fin.cases U (Fin.cases n
    (Fin.cases F (Fin.cases E (Fin.cases R (Fin.cases X (Fin.cases D (fun _ => b))))))))))), fun _ => b⟩
  let φ : UnarySchema 12 := {
    body := rs_los_m (𝒞 := kpair_convention_l) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Rs_los_d I b D X R E F n U p C T K s := rs_los_sat_l I hZF.1 ..
  suffices h : φ.denote ρ r from (sat r).mp h
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (sat r).mpr
  intro a e ha he hv
  have repr := hv.repr_l I ((hE a).mp ha).1
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  have trace s (hs : M.mem s n) : ∃ A, M.mem A P ∧
      ∀ v, M.mem v A ↔ M.mem v D ∧ Pe_sat_d I b D X R E F n s a v := by
    obtain ⟨A, hAX, hA⟩ := sc_pe_trace_l hZF hω hX hm theory hD hE hF hs hb hB ha repr
    exact ⟨A, (hP A).mpr ⟨hAX, fun v hv => ((hA v).mp hv).1⟩, hA⟩
  obtain ⟨z, hz⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r z hz with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨hib, hjb⟩ := hB.operands_l I hz hs
    obtain ⟨g, B, hig, hg, hgp, hie⟩ := hv i hib
    obtain ⟨f, A, hjf, hf, hfp, hje⟩ := hv j hjb
    have atom : Pe_holds_d I b D X R E F n r U a ↔ Rp_rel_d I X U R g f := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      apply forall_congr'
      intro v
      apply imp_congr_right
      intro hvW
      have hvD := hU.base.bounds W hW v hvW
      have read x y (hx : Rd_entry_d v x g) (hy : Rd_entry_d v y f) :=
        pe_sat_atom_l I hZF ext hE hF hV hB bω ha repr (hX D hD v hvD) (point v hvD) hz false hs hig hjf ((rf_val_mem_l I hZF.1 hX hm (hg.mem_l I)).mpr hx)
          ((rf_val_mem_l I hZF.1 hX hm (hf.mem_l I)).mpr hy)
      refine ⟨fun ht => ?_, fun ⟨x, _, y, _, hx, hy, hxy⟩ => (read x y hx hy).mpr hxy⟩
      obtain ⟨x, hx, hvx⟩ := (((rf_fun_mem_l I hZF.1 hX hm hD).mp hg).function_l hX).2.1 v hvD
      obtain ⟨y, hy, hvy⟩ := (((rf_fun_mem_l I hZF.1 hX hm hD).mp hf).function_l hX).2.1 v hvD
      exact ⟨x, hx, y, hy, hvx, hvy, (read x y hvx hvy).mp ht⟩
    exact atom.trans ((hM.relation g f B A hgp hfp).symm.trans (ssat_rel_l I hZF hF hJ hz hs hK he hie hje).symm)
  · obtain ⟨hib, hjb⟩ := hB.operands_l I hz hs
    obtain ⟨g, B, hig, hg, hgp, hie⟩ := hv i hib
    obtain ⟨f, A, hjf, hf, hfp, hje⟩ := hv j hjb
    have atom : Pe_holds_d I b D X R E F n r U a ↔ Rp_eq_d X U g f := by
      apply exists_congr
      intro W
      apply and_congr_right
      intro hW
      apply forall_congr'
      intro v
      apply imp_congr_right
      intro hvW
      have hvD := hU.base.bounds W hW v hvW
      have read x y (hx : Rd_entry_d v x g) (hy : Rd_entry_d v y f) :=
        pe_sat_atom_l I hZF ext hE hF hV hB bω ha repr (hX D hD v hvD) (point v hvD) hz true hs hig hjf ((rf_val_mem_l I hZF.1 hX hm (hg.mem_l I)).mpr hx)
          ((rf_val_mem_l I hZF.1 hX hm (hf.mem_l I)).mpr hy)
      refine ⟨fun ht => ?_, fun ⟨x, _, hx, hy⟩ => (read x x hx hy).mpr rfl⟩
      obtain ⟨x, hx, hvx⟩ := (((rf_fun_mem_l I hZF.1 hX hm hD).mp hg).function_l hX).2.1 v hvD
      obtain ⟨y, _, hvy⟩ := (((rf_fun_mem_l I hZF.1 hX hm hD).mp hf).function_l hX).2.1 v hvD
      exact ⟨x, hx, hvx, ((read x y hvx hvy).mp ht).symm ▸ hvy⟩
    exact atom.trans ((rp_kernel_l I hZF.1 hU.base hM.map hgp hfp).symm.trans
      (ssat_eq_l I hZF hF hJ hz hs hK he hie hje).symm)
  · have hin := hF.2.1.1.transitive r hr i hi
    have hjn := hF.2.1.1.transitive r hr j hj
    obtain ⟨A, hA, hsA⟩ := trace i hin
    obtain ⟨B, hB', hb'⟩ := trace j hjn
    obtain ⟨W, hW, hw⟩ := trace r hr
    exact (pe_holds_nor_l I hU hA hB' hW hsA hb' hw
      (fun v hvD => pe_sat_nor_l I hZF ext hE hF hV hB bω ha repr (hX D hD v hvD) (point v hvD) hz hs hin hjn)).trans
      ((not_congr (or_congr ((sat i).mp (ih i hi) a e ha he hv)
        ((sat j).mp (ih j hj) a e ha he hv))).trans (ssat_nor_l I hZF hF hJ hz hs he).symm)
  · have hjn := hF.2.1.1.transitive r hr j hj
    rw [ssat_exists_l I hZF hF hJ hz hs he]
    constructor
    · rintro ⟨A, hA, ht⟩
      obtain ⟨g, a', hg, ha', hs'⟩ := sc_pe_witness_l hZF hω hX hm theory uniform hD hE hF hV hz hs hjn hb hB
        ha ((hP A).mp (hU.admissible A hA)).1 (hU.base.bounds A hA) ht
      obtain ⟨B, hBC, hgp⟩ := hM.map.projection.2.2 g ((hG g).mpr ⟨hg.1, hg.function_l hX⟩)
      obtain ⟨e', he', heK⟩ := senv_update_exists_l I hZF ((hK e).mp he) hi hBC
      exact ⟨B, e', hBC, he', ((sat j).mp (ih j hj) a' e'
        ((hE a').mpr (ha'.function_l I ((hE a).mp ha) hi hg.1)) ((hK e').mpr heK)
        (hv.update_l I ((rf_fun_mem_l I hZF.1 hX hm hD).mpr hg) hgp ha' he')).mp ⟨A, hA, hs'⟩⟩
    · rintro ⟨B, e', hBC, he', ht⟩
      obtain ⟨g, hgp⟩ := (hM.map.range B).mp hBC
      obtain ⟨hgX, hgD⟩ := (hG g).mp (hM.map.projection.input_mem_of_pairMember hgp)
      have hg := sc_function_domain_l (theory.algebra_l _ (ZF.modelsKP hZF) hX hm) hgX hgD
      obtain ⟨a', ha', haE⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hi hgX
      obtain ⟨A, hA, hA'⟩ := ((sat j).mp (ih j hj) a' e' ((hE a').mpr haE)
        ((hK e').mpr (he'.function_l I ((hK e).mp he) hi hBC)) (hv.update_l I ((rf_fun_mem_l I hZF.1 hX hm hD).mpr hg) hgp ha' he')).mpr ht
      exact ⟨A, hA, fun v hvA => pe_sat_ex_intro_l I hZF ext hE hF hV hB bω ha repr
        (hX D hD v (hU.base.bounds A hA v hvA)) (point v (hU.base.bounds A hA v hvA)) hz hs hi hjn
        ((rf_fun_mem_l I hZF.1 hX hm hD).mpr hg) ha' (hA' v hvA)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 全部源内部公式代码的商满足关系

同一个实际代表赋值投影为同一个商赋值。逐公式取得有限支撑后应用行定理，
再用全坐标逐点赋值消去支撑参数，得到统一满足关系上的完整 Łoś 方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c X R D P U o G p C T E}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (uniform : Sc_uniform_d (kp_pair_l (ZF.modelsKP hZF)) ω X R D)
    (hD : M.mem D X) (hP : FilterZF.Source_d X D P)
    (hU : FilterZF.Rel_ultra_d D P U) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hM : Rp_model_d (kp_pair_l (ZF.modelsKP hZF)) D X U R o G p C T)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E ω X)
include hω hX hm theory uniform hD hP hU hG hM hE

theorem rs_satisfies_l {A a e z} (hA : Scode_d I ω A) (ha : M.mem a E)
    (he : M.IsSetFunctionFromTo I e ω C) (hv : Rs_eval_d I ω D X R p a e) (hz : M.mem z A) :
    Satisfies_d I ω o z e ↔ ∃ B, M.mem B U ∧ ∀ v, M.mem v B →
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D X R a f v ∧ Satisfies_d I ω c z f := by
  obtain ⟨n, F, r, hf⟩ := (hA z).mp hz
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hf.2.1
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  have bω := hω.transitive (ZF.modelsKP hZF) b hb
  have repr := hv.repr_l I ((hE a).mp ha).1
  have los := rs_los_l hZF hω hX hm theory uniform hD hP hU hG hM hE hK hf.2.1 hb hB hf.2.2
    a e ha ((hK e).mpr he) (fun i hi => hv i (bω i hi))
  refine (satisfies_decode_l I hZF.1 hM.code hf hK).trans (los.symm.trans ?_)
  apply exists_congr
  intro B
  apply and_congr_right
  intro hB'
  apply forall_congr'
  intro v
  apply imp_congr_right
  intro hvB
  have hvD := hU.base.bounds B hB' v hvB
  apply (pe_sat_full_l I hZF (rf_ext_mem_l I hZF.1 hX hm) hE hf.2.1 hB bω hf.2.2 ha repr (hX D hD v hvD) ((hm.2 v D).mpr ⟨hX D hD v hvD, hD, hvD⟩)).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 hm.1 hf hE).symm

omit hE in
/-- 从实际 ω→G 代表赋值图一次构造赋值空间、商赋值和全部公式码。 -/
theorem rs_los_assignment_l {a} (ha : M.IsSetFunctionFromTo I a ω G) : ∃ E e A,
    M.IsFunctionSpace I E ω X ∧ M.IsSetFunctionFromTo I e ω C ∧ Rs_eval_d I ω D X R p a e ∧ Scode_d I ω A ∧
    ∀ z, M.mem z A → (Satisfies_d I ω o z e ↔ ∃ B, M.mem B U ∧ ∀ v, M.mem v B →
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D X R a f v ∧ Satisfies_d I ω c z f) := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have hax : M.IsSetFunctionFromTo I a ω X := ⟨ha.1, ha.2.1, fun i hi =>
    (ha.2.2 i hi).imp fun g hg => ⟨((hG g).mp hg.1).1, hg.2⟩⟩
  have hr : Pe_repr_d I ω D X R a := fun i g _ hg => by
    obtain ⟨hgX, hgD⟩ := (hG g).mp (ha.output_mem_of_pairMember hg)
    exact (rf_fun_mem_l I hZF.1 hX hm hD).mpr (sc_function_domain_l (theory.algebra_l _ (ZF.modelsKP hZF) hX hm) hgX hgD)
  obtain ⟨e, he, hv⟩ := rs_eval_exists_l I hZF (fun g hg => (hG g).mpr
    ⟨hg.mem_l I, ((rf_fun_mem_l I hZF.1 hX hm hD).mp hg).function_l hX⟩) hM.map.projection hE ((hE a).mpr hax) hr
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  exact ⟨E, e, A, hE, he, hv, hA, fun z hz => rs_satisfies_l hZF hω hX hm theory uniform hD hP hU hG hM hE
    hA ((hE a).mpr hax) he hv hz⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内部超幂的常值初等嵌入

先收集每个源对象的唯一常值图，再与实际商投影复合。源内部 Łoś 把常值
赋值的逐点真值还原为原真值，得到覆盖全部内部代码的 Smap 证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Rs_const_d (D x f : M.Domain) : Prop := ∀ v, M.mem v D → Rd_entry_d v x f

def rs_const_m {d} (D x f : Term d) : Formula 1 d :=
  Formula.forallMem D (rd_entry0_m .newest x.weaken f.weaken)
derive_free_closed rs_const_m

theorem rs_const_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D x f : Term d) :
    Formula.satisfies ρ (rs_const_m D x f) ↔ Rs_const_d (D.eval ρ) (x.eval ρ) (f.eval ρ) := by
  simp only [rs_const_m, Rs_const_d, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rs_const_unique_l (hE : Extensional M) {D X Y x f g : M.Domain}
    (hf : Fn0_d D X f) (hg : Fn0_d D Y g) (h : Rs_const_d D x f) (k : Rs_const_d D x g) : f = g :=
  hf.ext_l hE hg (fun v hv => ⟨x, h v hv, k v hv⟩)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_constants_l {ω c X R D G} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X)
    (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g) : ∃ K, M.IsSetFunctionFromTo I K X G ∧
      ∀ x f, M.PairMember I x f K ↔ M.mem x X ∧ M.mem f G ∧ Rs_const_d D x f := by
  let ρ : Env M 2 := ⟨Fin.cases G (fun _ => D), fun _ => D⟩
  let φ : BinarySchema 2 := { body := .conj (.mem .newest (.bound 2)) (rs_const_m (.bound 3) (.bound 1) .newest) }
  have sat x f : φ.denote ρ x f ↔ M.mem f G ∧ Rs_const_d D x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rs_const_sat_l hZF.1]
    rfl
  obtain ⟨K, hK, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := X) (target := G)
    (fun x hx => by
      obtain ⟨f, C, hf, hC, hFC, hc⟩ := sc_constant_l hZF hω hX hm theory hD hx
      exact ⟨f, (sat x f).mpr ⟨(hG f).mpr ⟨hf, hFC.mono_target_l (hX C hC)⟩,
        fun v hv => (hc v x).mpr ⟨hv, rfl⟩⟩⟩)
    (fun x _ f g hf hg => rs_const_unique_l hZF.1 ((hG f).mp ((sat x f).mp hf).1).2
      ((hG g).mp ((sat x g).mp hg).1).2 ((sat x f).mp hf).2 ((sat x g).mp hg).2)
    (fun x f _ hf => ((sat x f).mp hf).1)
  exact ⟨K, hK, fun x f => (spec x f).trans (and_congr_right fun _ => sat x f)⟩

theorem rs_constant_embedding_l {ω c X R D P U o G p C T}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hP : FilterZF.Source_d X D P)
    (hU : FilterZF.Rel_ultra_d D P U) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hM : Rp_model_d I D X U R o G p C T) : ∃ j, Smap_d I ω c o X C j ∧
      ∀ x B, M.PairMember I x B j ↔ M.mem x X ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ M.PairMember I f B p := by
  obtain ⟨K, hK, hc⟩ := rs_constants_l hZF hω hX hm theory hD hG
  obtain ⟨j, hj, spec⟩ := ZF.exists_compositionFunction hZF I hK hM.map.projection
  have value x f (hf : M.PairMember I x f K) := ((hc x f).mp hf).2.2
  have inj : M.IsSetInjectionFromTo I j X C := ⟨hj, fun x y B hx hy => by
    obtain ⟨_, f, hxf, hf⟩ := (spec x B).mp hx
    obtain ⟨_, g, hyg, hg⟩ := (spec y B).mp hy
    obtain ⟨A, hA, he⟩ := (rp_kernel_l I hZF.1 hU.base hM.map hf hg).mp rfl
    obtain ⟨v, hv⟩ := hU.proper A hA
    obtain ⟨z, _, hvf, hvg⟩ := he v hv
    have hvD := hU.base.bounds A hA v hv
    have ex := (fn0_function_l (ZF.modelsKP hZF) (hM.map.functions f (hK.output_mem_of_pairMember hxf))).1.2
      v x z (value x f hxf v hvD) hvf
    have ey := (fn0_function_l (ZF.modelsKP hZF) (hM.map.functions g (hK.output_mem_of_pairMember hyg))).1.2
      v y z (value y g hyg v hvD) hvg
    exact ex.trans ey.symm⟩
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨j, ⟨inj, A, hA, fun z f e hz hf he hfe => ?_⟩, fun x B => (spec x B).trans (and_congr_right fun hx => ?_)⟩
  · obtain ⟨a, ha, hfa⟩ := ZF.exists_compositionFunction hZF I hf hK
    have haX : M.IsSetFunctionFromTo I a ω X := ⟨ha.1, ha.2.1, fun i hi =>
      (ha.2.2 i hi).imp fun g hg => ⟨((hG g).mp hg.1).1, hg.2⟩⟩
    have sfun g (hg : M.mem g G) := (rf_fun_mem_l I hZF.1 hX hm hD).mpr
      (sc_function_domain_l (theory.algebra_l _ (ZF.modelsKP hZF) hX hm) ((hG g).mp hg).1 ((hG g).mp hg).2)
    have eval : Rs_eval_d I ω D X R p a e := by
      intro i hi
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨g, hg, hxg⟩ := hK.2.2 x hx
      obtain ⟨B, _, hgp⟩ := hM.map.projection.2.2 g hg
      exact ⟨g, B, (hfa i g).mpr ⟨hi, x, hix, hxg⟩, sfun g hg, hgp,
        hfe i hi x B hix ((spec x B).mpr ⟨hx, g, hxg, hgp⟩)⟩
    have point v (hv : M.mem v D) : Pe_assign_d I ω D X R a f v := by
      intro i hi
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨g, hg, hxg⟩ := hK.2.2 x hx
      exact ⟨g, x, (hfa i g).mpr ⟨hi, x, hix, hxg⟩, sfun g hg, (rf_val_mem_l I hZF.1 hX hm ((hG g).mp hg).1).mpr (value x g hxg v hv), hix⟩
    have los := rs_satisfies_l hZF hω hX hm theory uniform hD hP hU hG hM hE hA ((hE a).mpr haX) he eval hz
    refine ⟨fun hs => los.mpr ⟨D, hU.base.top, fun v hv => ⟨f, (hE f).mpr hf, point v hv, hs⟩⟩, fun hs => ?_⟩
    obtain ⟨B, hB, hb⟩ := los.mp hs
    obtain ⟨v, hv⟩ := hU.proper B hB
    obtain ⟨g, hg, hval, hs⟩ := hb v hv
    have agree := hval.agree_right_l I (point v (hU.base.bounds B hB v hv)) (rf_ext_mem_l I hZF.1 hX hm) haX.1 ((hE g).mp hg).1 hf.1
    have eq : g = f := ((hE g).mp hg).1.1.eq_of_pairMember_iff hZF.1 hf.1.1
      (fun i x => ⟨fun h => (agree i x (((hE g).mp hg).input_mem_of_pairMember h)).mp h,
        fun h => (agree i x (hf.input_mem_of_pairMember h)).mpr h⟩)
    exact eq ▸ hs
  · exact ⟨fun ⟨f, hxf, hfp⟩ => ⟨f, ((hc x f).mp hxf).2.1, value x f hxf, hfp⟩,
      fun ⟨f, hf, hconst, hfp⟩ => ⟨f, (hc x f).mpr ⟨hx, hf, hconst⟩, hfp⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系后继中的共同有界代表族

原关系函数码与共同低层中的有界函数逐一对应。方向之一回收新函数码，
另一方向将同层的原图沿完整实现读出；两侧使用同一实际复合图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_bounded_functions_l {Y S H Γ k D A t G : M.Domain}
    (ny : ∃ y, M.mem y Y) (ext : Rf_ext_d I Y S) (closed : Rr_closed_d I Y S H)
    (hΓ : M.TransitiveSet Γ) (algebra : Sc_algebra_d Γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (d a : (smdl_structure_l I (R := S) ny).Domain)
    (hD : Rd_entry_d D d.val k) (hA : Rd_entry_d A a.val k) (ht : M.IsRestrictionOf I t k D)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) ny).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) :
    ∀ g, (M.mem g G ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y a.val S) ↔
      ∃ F, M.mem F Γ ∧ Fn0_d D A F ∧ Cp0_d D Γ Y F k g := by
  have hDG := fk.1.input_mem_of_pairMember hD
  have hAG := fk.1.input_mem_of_pairMember hA
  have en := ext.native_l I ny
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (hΓ D hDG))
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have code {F : M.Domain} {f : (smdl_structure_l I (R := S) ny).Domain}
      (fn : Fn0_d D A F) (hFf : Rd_entry_d F f.val k)
      (g : M.Domain) (fg : Fn0_d D Y g) :
      (∀ s (x y : (smdl_structure_l I (R := S) ny).Domain), Rd_entry_d s x.val t →
        (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ↔ Cp0_d D Γ Y F k g := by
    obtain ⟨ff, read⟩ := rr_realize_function_l I hZF.1 hΓ ny ext fk pred a d f hA hD hFf fn
    constructor
    · intro decode
      refine ⟨fg, fun s hs => ?_⟩
      obtain ⟨v, hv, hsv⟩ := fn.2.1 s hs
      obtain ⟨y, hy, hvy⟩ := fk.1.2.2 v (hΓ A hAG v hv)
      obtain ⟨x, hx, hsx⟩ := ft.2.1 s hs
      exact ⟨v, hΓ A hAG v hv, y, hy, hsv, hvy, (decode s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mpr
        ((rf_val_native_l I ny en ..).mp (read s v x y hsv ((ht.2 s x).mp hsx).2 hvy))⟩
    · intro comp s x y hsx
      obtain ⟨v, hv, hsv⟩ := fn.2.1 s (ft.bound_l hsx).1
      obtain ⟨z, hz, hvz⟩ := fk.1.2.2 v (hΓ A hAG v hv)
      have value := (rf_val_native_l I ny en x ⟨z, hz⟩ f).mp
        (read s v x.val z hsv ((ht.2 s x.val).mp hsx).2 hvz)
      have bound := fn.mono_target_l (hΓ A hAG)
      have graph := (comp.value_l bound key hsv).mpr hvz
      constructor
      · intro h
        have eq : (⟨z, hz⟩ : (smdl_structure_l I (R := S) ny).Domain) = y :=
          Subtype.ext (fg.2.2 s (ft.bound_l hsx).1 z hz y.val y.property graph h)
        exact eq ▸ value
      · intro h
        exact congrArg Subtype.val (ff.2.2 x (ff.bound_l h).1 ⟨z, hz⟩ (ff.bound_l value).2 y (ff.bound_l h).2 value h) ▸ graph
  intro g
  constructor
  · rintro ⟨hg, bounded⟩
    obtain ⟨fg, B', f, ff, decode⟩ := (hG g).mp hg
    have ff' : Fn0_d d a f := ff.retarget_l (fun x y hxy => by
      obtain ⟨s, hs, hsx⟩ := (pred D d.val hD x.val).mp (ff.bound_l hxy).1
      exact bounded s y.val ((decode s x y ((ht.2 s x.val).mpr ⟨hs, hsx⟩)).mpr hxy))
    obtain ⟨P, hP, product⟩ := algebra.product D A hDG hAG
    obtain ⟨F, hF, hFf, fn⟩ := rr_capture_function_l hZF ny ext closed hΓ fk image pred d a f hD hA hP product ff'
    exact ⟨F, hF, fn, (code fn hFf g fg).mp decode⟩
  · rintro ⟨F, hF, fn, comp⟩
    obtain ⟨f, hf, hFf⟩ := fk.1.2.2 F hF
    obtain ⟨ff, _⟩ := rr_realize_function_l I hZF.1 hΓ ny ext fk pred a d ⟨f, hf⟩ hA hD hFf fn
    refine ⟨(hG g).mpr ⟨comp.1, a, ⟨f, hf⟩, ff, (code (f := ⟨f, hf⟩) fn hFf g comp.1).mpr comp⟩, fun s y hsy => ?_⟩
    obtain ⟨v, hv, hsv⟩ := fn.2.1 s (comp.1.bound_l hsy).1
    exact (pred A a.val hA y).mpr ⟨v, hv, (comp.value_l (fn.mono_target_l (hΓ A hAG)) key hsv).mp hsy⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系商中低层成员的处处有界代表

只在测度零处改值。修改关系直接在当前原结构的乘积中分离，
其有界函数图仍属于同一原关系源；原子 Łoś 识别同一个商元素。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_bound_raw_l {ω c' Y S : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (theory : Sc_theory_d I ω Y S)
    (ext : Rf_ext_d I Y S) (d b a f z : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ff : Fn0_d d b f) (hz : Rd_entry_d z.val a.val S) :
    ∃ g : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d d a g ∧
      ∀ x y, Rd_entry_d x.val d.val S → Rd_entry_d y.val a.val S → Rd_entry_d x y f → Rd_entry_d x y g := by
  let N := smdl_structure_l I (R := S) model.2.1
  have en := ext.native_l I model.2.1
  let ρ : Env N 0 := ⟨Fin.elim0, fun _ => d⟩
  have algebra := theory.algebra model.2.1 ρ
  obtain ⟨P, prod⟩ := algebra.1.2.2.1 d a
  change Formula.satisfies (((ρ.push d).push a).push P) (ri_image_m .prod (.bound 2) (.bound 1) .newest) at prod
  simp only [ri_image_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, ri_value_sat_l en, ri_guard_sat_l en,
    Definitional.Term.eval_weaken] at prod
  change (∀ p, N.mem p P → ∃ x, N.mem x d ∧ ∃ y, N.mem y a ∧ KPair_d N p x y) ∧
    (∀ x, N.mem x d → ∀ y, N.mem y a → True → ∃ p, N.mem p P ∧ KPair_d N p x y) at prod
  let η : Env N 4 := ⟨Fin.cases z (Fin.cases f (Fin.cases a (fun _ => d))), fun _ => d⟩
  let φ : UnarySchema 4 := { body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 4)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest)
      (.disj (rd_entry0_m (.bound 1) .newest (.bound 4))
        (.conj (.neg (Formula.existsMem (.bound 5) (rd_entry0_m (.bound 2) .newest (.bound 5))))
          (Formula.extensionalEq .newest (.bound 3)))))) }
  let good x y := Rd_entry_d x y f ∨ (¬ (∃ v, N.mem v a ∧ Rd_entry_d x v f) ∧ y = z)
  have read p : φ.denote η p ↔ ∃ x, N.mem x d ∧ ∃ y, N.mem y a ∧ KPair_d N p x y ∧ good x y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, kpair0_sat_l en, rd_entry0_sat_l en,
      Formula.satisfies_extensionalEq_iff_eq en]; rfl
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c') hω
  obtain ⟨Q₀, hQ, sep⟩ := sc_separate_raw_l I hZF hω model theory model identity φ η P
  let Q : N.Domain := ⟨Q₀, hQ⟩
  have graph x y : Rd_entry_d x y Q ↔ N.mem x d ∧ N.mem y a ∧ good x y := by
    constructor
    · rintro ⟨p, pair, hp⟩
      obtain ⟨u, hu, v, hv, pv, point⟩ := (read p).mp ((sep p).mp hp).2
      obtain ⟨rfl, rfl⟩ := kpair_injective_l N pv pair
      exact ⟨hu, hv, point⟩
    · rintro ⟨hx, hy, point⟩
      obtain ⟨p, hp, pair⟩ := prod.2 x hx y hy trivial
      exact ⟨p, pair, (sep p).mpr ⟨hp, (read p).mpr ⟨x, hx, y, hy, pair, point⟩⟩⟩
  have total : ∀ x, N.mem x d → ∃ y, N.mem y a ∧ Rd_entry_d x y Q := by
    intro x hx
    classical
    by_cases h : ∃ y, N.mem y a ∧ Rd_entry_d x y f
    · obtain ⟨y, hy, hxy⟩ := h
      exact ⟨y, hy, (graph x y).mpr ⟨hx, hy, Or.inl hxy⟩⟩
    · exact ⟨z, hz, (graph x z).mpr ⟨hx, hz, Or.inr ⟨h, rfl⟩⟩⟩
  -- 分离关系已经单值，直接取它作修改图，不调用源内选择。
  refine ⟨Q, ⟨?_, total, ?_⟩, fun x y hx hy hxy => (graph x y).mpr ⟨hx, hy, Or.inl hxy⟩⟩
  · intro p hp
    obtain ⟨x, hx, y, hy, pair, _⟩ := (read p).mp ((sep p).mp hp).2
    exact ⟨x, hx, y, hy, pair⟩
  · intro x hx y hy v hv hxy hxv
    rcases ((graph x y).mp hxy).2.2 with hf | ⟨no, eq⟩
    · rcases ((graph x v).mp hxv).2.2 with hf' | ⟨no, _⟩
      · exact ff.2.2 x hx y (ff.bound_l hf).2 v (ff.bound_l hf').2 hf hf'
      · exact (no ⟨y, hy, hf⟩).elim
    · rcases ((graph x v).mp hxv).2.2 with hf | ⟨_, eq'⟩
      · exact (no ⟨v, hv, hf⟩).elim
      · exact eq.trans eq'.symm

theorem rc_bounded_representative_l {ω c' Y S D t U G o p C T a A E : M.Domain}
    (hω : M.IsOmega ω) (source : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (ft : Fn0_d D Y t)
    (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hU : Base_d D U) (proper : Proper_d U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T)
    (value : M.mem a Y ∧ ∃ f, M.mem f G ∧ Rs_const_d D a f ∧ Rd_entry_d f A p)
    (edge : Rd_entry_d E A T) :
    ∃ g, M.mem g G ∧ Rd_entry_d g E p ∧
      (∀ s y, Rd_entry_d s y g → Rd_entry_d y a S) ∧
      ∃ f : (smdl_structure_l I (R := S) source.2.1).Domain,
        Fn0_d d ⟨a,value.1⟩ f ∧ Rc_graph_d I Y S t f.val g := by
  obtain ⟨ha, k, hk, constant, hkA⟩ := value
  obtain ⟨f, hfE⟩ := (model.map.range E).mp (model.code.2.2.2 E A edge).1
  obtain ⟨_, B, F, ff, decode⟩ := (hG f).mp (model.map.projection.input_mem_of_pairMember hfE)
  obtain ⟨P, hP, point⟩ := (model.relation f k E A hfE hkA).mp edge
  have bounded s (hs : M.mem s P) : ∃ y, M.mem y Y ∧ Rd_entry_d s y f ∧ Rd_entry_d y a S := by
    obtain ⟨y, hy, z, _, hsy, hsz, hyz⟩ := point s hs
    have eq := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions k hk)).1.2 s z a hsz (constant s (hU.bounds P hP s hs))
    exact ⟨y, hy, hsy, eq ▸ hyz⟩
  obtain ⟨s₀, hs₀⟩ := proper P hP
  obtain ⟨z, hz, _, hza⟩ := bounded s₀ hs₀
  obtain ⟨F', ff', agree⟩ := sc_bound_raw_l hZF hω source theory ext d B ⟨a, ha⟩ F ⟨z, hz⟩ ff hza
  obtain ⟨g, gg, decode'⟩ := smdl_function_l hZF source.2.1 (ext.native_l I source.2.1) d ⟨a, ha⟩ F' ff' ft domain
  have hg := (hG g).mpr ⟨gg, ⟨a, ha⟩, F', ff', decode'⟩
  obtain ⟨E', _, hgE⟩ := model.map.projection.2.2 g hg
  have eq : E = E' := (rp_kernel_l I hZF.1 hU model.map hfE hgE).mpr ⟨P, hP, fun s hs => by
    obtain ⟨y, hy, hsy, hya⟩ := bounded s hs
    obtain ⟨x, hx, hsx⟩ := ft.2.1 s (hU.bounds P hP s hs)
    exact ⟨y, hy, hsy, (decode' s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mpr
      (agree ⟨x, hx⟩ ⟨y, hy⟩ (domain s x hsx) hya ((decode s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mp hsy))⟩⟩
  -- 保留处处有界的原生函数码，供后续幂集编码计数。
  refine ⟨g, hg, eq.symm ▸ hgE, ?_, F', ff', ?_⟩
  · intro s y hsy
    obtain ⟨x, hx, hsx⟩ := ft.2.1 s (gg.bound_l hsy).1
    exact (ff'.bound_l ((decode' s ⟨x, hx⟩ ⟨y, (gg.bound_l hsy).2⟩ hsx).mp hsy)).2
  · exact (rc_graph_native_l I source.2.1 (ext.native_l I source.2.1) ft gg F').mpr decode'

/-- 下一商的低层恰由共同层中的有界图覆盖，包括全部新商成员。 -/
theorem Rp_model_d.low_cover_raw_l {ω c X R c' Y S q H Γ k D A t U G o p C T j A' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (trans : M.TransitiveSet Γ) (algebra : Sc_algebra_d Γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (d a : (smdl_structure_l I (R := S) source.2.1).Domain)
    (hD : Rd_entry_d D d.val k) (hA : Rd_entry_d A a.val k) (ht : M.IsRestrictionOf I t k D)
    (hU : Base_d D U) (proper : Proper_d U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T)
    (constants : ∀ x B, Rd_entry_d x B j ↔ M.mem x Y ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B p)
    (ha : Rd_entry_d a.val A' j) : ∀ E, Rd_entry_d E A' T ↔
      ∃ F g, M.mem F Γ ∧ Fn0_d D A F ∧ Cp0_d D Γ Y F k g ∧ Rd_entry_d g E p := by
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (trans D (fk.1.input_mem_of_pairMember hD)))
  have domain s x (hsx : Rd_entry_d s x t) := (pred D d.val hD x).mpr
    ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm.1 source (rf_ext_mem_l I hZF.1 hX hm)
  have common := rr_bounded_functions_l hZF source.2.1 ext closed trans algebra fk image pred d a hD hA ht hG
  intro E
  constructor
  · intro edge
    obtain ⟨g, hg, hgE, bound, _⟩ := rc_bounded_representative_l hZF hω source ext
      (theory.map_l I hZF hω hm.1 source hq) d ft domain hU proper hG model
      ((constants a.val A').mp ha) edge
    obtain ⟨F, hF, fn, comp⟩ := (common g).mp ⟨hg, bound⟩
    exact ⟨F, g, hF, fn, comp, hgE⟩
  · rintro ⟨F, g, hF, fn, comp, hgE⟩
    obtain ⟨hg, bound⟩ := (common g).mpr ⟨F, hF, fn, comp⟩
    obtain ⟨_, f, _, constant, hfA⟩ := (constants a.val A').mp ha
    apply (model.relation g f E A' hgE hfA).mpr
    refine ⟨D, hU.top, fun s hs => ?_⟩
    obtain ⟨y, hy, hsy⟩ := (model.map.functions g hg).2.1 s hs
    exact ⟨y, hy, a.val, a.property, hsy, constant s hs, bound s y hsy⟩

end YesMetaZFC.SetTheory.Internal

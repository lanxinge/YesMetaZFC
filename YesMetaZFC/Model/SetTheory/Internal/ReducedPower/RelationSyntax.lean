import YesMetaZFC.Model.SetTheory.Internal.RelationFunctionFamily
import YesMetaZFC.Model.SetTheory.Internal.RelationTraceFamily
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSyntax

/-! # 原关系函数码、实际坐标图与商赋值

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

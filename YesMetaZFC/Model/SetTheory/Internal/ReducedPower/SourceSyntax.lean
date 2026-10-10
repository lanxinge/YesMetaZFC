import YesMetaZFC.Model.SetTheory.Internal.PointwiseAssignment
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model

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

def Rs_eval_d (b D X p a e : M.Domain) : Prop := ∀ i, M.mem i b → ∃ g B,
  M.PairMember I i g a ∧ Sfun_d X D g ∧ M.PairMember I g B p ∧ M.PairMember I i B e

def rs_eval_m {d} (b D X p a e : Term d) : Formula 1 d := Formula.forallMem b (.existsE (.existsE
  (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) a.weaken.weaken.weaken)
    (.conj (sfun_m X.weaken.weaken.weaken D.weaken.weaken.weaken (.bound 1))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken.weaken)
        (Formula.orderedPairMem 𝒞 (.bound 2) .newest e.weaken.weaken.weaken))))))
derive_free_closed rs_eval_m

theorem rs_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b D X p a e : Term d) :
    Formula.satisfies ρ (rs_eval_m (𝒞 := 𝒞) b D X p a e) ↔
      Rs_eval_d I (b.eval ρ) (D.eval ρ) (X.eval ρ) (p.eval ρ) (a.eval ρ) (e.eval ρ) := by
  simp only [rs_eval_m, Rs_eval_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, sfun_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Rs_eval_d.repr_l {b D X p a e} (h : Rs_eval_d I b D X p a e)
    (ha : M.IsSetFunction I a) : Pe_repr_d I b D X a := by
  intro i g hi hg
  obtain ⟨g', _, hg', hG, _⟩ := h i hi
  exact ha.2 i g' g hg' hg ▸ hG

theorem Rs_eval_d.update_l {b D X p a e i g B a' e'} (h : Rs_eval_d I b D X p a e)
    (hg : Sfun_d X D g) (hp : M.PairMember I g B p) (ha : Senv_update_d I a i g a')
    (he : Senv_update_d I e i B e') : Rs_eval_d I b D X p a' e' := by
  intro j hj
  by_cases eq : j = i
  · exact ⟨g, B, (ha.2 j g).mpr (Or.inl ⟨eq, rfl⟩), hg, hp, (he.2 j B).mpr (Or.inl ⟨eq, rfl⟩)⟩
  · obtain ⟨f, C, hf, hF, hp, hc⟩ := h j hj
    exact ⟨f, C, (ha.2 j f).mpr (Or.inr ⟨eq, hf⟩), hF, hp, (he.2 j C).mpr (Or.inr ⟨eq, hc⟩)⟩

def Rs_los_d (b D X R E F n U p C T K r : M.Domain) : Prop := ∀ a e,
  M.mem a E → M.mem e K → Rs_eval_d I b D X p a e →
    (Pe_holds_d I b D X R E F n r U a ↔ Ssat_d I C T K F n r e)

def rs_los_m {d} (b D X R E F n U p C T K r : Term d) : Formula 1 d :=
  Formula.forallMem E (Formula.forallMem K.weaken
    (.imp (rs_eval_m (𝒞 := 𝒞) b.weaken.weaken D.weaken.weaken X.weaken.weaken p.weaken.weaken (.bound 1) .newest)
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
    rs_eval_sat_l I hE, Formula.satisfies_iff_iff, pe_holds_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h a e ha he => h a ha e he, fun h a ha e he => h a e ha he⟩

end YesMetaZFC.SetTheory.Internal

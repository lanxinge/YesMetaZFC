import YesMetaZFC.Model.SetTheory.Internal.RelationEvaluation

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

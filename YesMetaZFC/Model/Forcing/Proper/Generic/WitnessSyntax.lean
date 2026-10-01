import YesMetaZFC.Model.Forcing.Proper.Generic.Witness

/-! # 泛型见证池的实际反射公式

名称参数保留为可变的 bound 槽位。完整的池、覆盖和判定方程共同组成一条原
公式，供通用 Lévy 反射使用，而不对 N 另加未实现的闭包合同。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def ng_decide_m {d} (B R z A D : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest D.weaken) (.conj (.mem .newest B.weaken)
    (.conj (.neg (Formula.extensionalEq .newest z.weaken)) (.disj
      (.existsE (entry_m .newest (.bound 1) A.weaken.weaken))
      (.forallE (.imp (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1))
        (.neg (.existsE (entry_m .newest (.bound 1) A.weaken.weaken.weaken)))))))))
derive_free_closed ng_decide_m

def ng_witness_m {n d} (φ : UnarySchema n) (e : Fin n → Term d) (B R z A D : Term d) : Formula 1 d :=
  .conj (name_m B A) (.conj
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest A.weaken.weaken)
      (force_at_m φ.body (Fin.cases (.bound 1) (fun i => (e i).weaken.weaken))
        B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest))))
    (.conj (.forallE (.forallE (.imp (.mem (.bound 1) B.weaken.weaken)
      (.imp (name_m B.weaken.weaken .newest)
        (.imp (force_at_m φ.body (Fin.cases .newest (fun i => (e i).weaken.weaken))
          B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1))
          (.existsE (entry_m .newest (.bound 2) A.weaken.weaken.weaken)))))))
      (ng_decide_m B R z A D)))

@[simp] theorem ng_witness_closed_l {n d} (φ : UnarySchema n) (e : Fin n → Term d) (B R z A D : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (hA : A.freeSupport = []) (hD : D.freeSupport = []) :
    (ng_witness_m φ e B R z A D).FreeClosed := by
  have hs (t : Term (d+2)) (ht : t.freeSupport = []) :
      ∀ i, (Fin.cases t (fun i => (e i).weaken.weaken) i : Term (d+2)).freeSupport = [] :=
    Fin.cases ht (fun i => by simpa using he i)
  simp -implicitDefEqProofs [ng_witness_m, Definitional.Formula.FreeClosed, φ.freeClosed, *]

theorem ng_witness_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n d}
    (φ : UnarySchema n) (ρ : Env M d) (e : Fin n → Term d) (B R z A D : Term d) :
    Formula.satisfies ρ (ng_witness_m φ e B R z A D) ↔
      Ng_witness_d (B := B.eval ρ) (R := R.eval ρ) (z := z.eval ρ) φ
        ⟨fun i => (e i).eval ρ, ρ.free⟩ (A.eval ρ) (D.eval ρ) := by
  simp only [ng_witness_m, ng_decide_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, name_sat_l M hE, entry_sat_l M hE,
    below_sat_l M hE, force_at_sat_l, args_cons_l, Definitional.Term.eval_weaken]
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  exact ⟨fun h => ⟨h.1, h.2.1, fun p hp s hs hf => h.2.2.1 p s hp hs hf, h.2.2.2⟩,
    fun h => ⟨h.name, h.sound, fun p s hp => h.cover p hp s, h.decide⟩⟩

def ng_data_m {n} (φ : UnarySchema n) : Formula 1 (n+5) :=
  ng_witness_m φ (fun i => .bound ⟨i.val+5, by omega⟩) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest

@[simp] theorem ng_data_closed_l {n} (φ : UnarySchema n) : (ng_data_m φ).FreeClosed :=
  ng_witness_closed_l _ _ _ _ _ _ _ (fun _ => rfl) rfl rfl rfl rfl rfl

def ng_exists_m {n} (φ : UnarySchema n) : Formula 1 (n+3) := .existsE (.existsE (ng_data_m φ))

@[simp] theorem ng_exists_closed_l {n} (φ : UnarySchema n) : (ng_exists_m φ).FreeClosed := by
  simp only [ng_exists_m, Definitional.Formula.FreeClosed, ng_data_closed_l]

theorem ng_data_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (φ : UnarySchema n)
    (ρ : Env M n) (B R z A D : M.Domain) :
    Formula.satisfies (((((ρ.push B).push R).push z).push A).push D) (ng_data_m φ) ↔
      Ng_witness_d (B := B) (R := R) (z := z) φ ρ A D := by
  have he : (⟨fun i => (Term.bound ⟨i.val+5, by omega⟩ : Term (n+5)).eval
      (((((ρ.push B).push R).push z).push A).push D), ρ.free⟩ : Env M n) = ρ := by cases ρ; rfl
  exact (ng_witness_sat_l hE φ _ _ _ _ _ _ _).trans (he ▸ Iff.rfl)

end YesMetaZFC.Model.Forcing.Internal

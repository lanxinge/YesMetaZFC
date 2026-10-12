import YesMetaZFC.Model.SetTheory.Internal.Builder

/-! # 原变量中一个内部有限区间的成员枚举

编译“x 等于某个非首坐标”的有限析取。沿模型自己的 ω 归纳，
输出仍为原程序；不把变量列重新打包，也不固定标签的排列次序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sg_any_d (ω e b n m G u : M.Domain) : Prop := ∀ X R E f x,
  M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I b x f →
    (Ssat_d I X R E G m u f ↔ ∃ i, M.mem i n ∧ i ≠ e ∧ M.PairMember I i x f)

def sg_any_m {d} (ω e b n m G u : Term d) : Formula 1 d := set[d] ⟪∀ X R E f x,
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E, ⌜ω⌝ₛ, X) → f ∈ E → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ, x, f) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔
      (∃ i ∈ ⌜n⌝ₛ, ¬ (i = ⌜e⌝ₛ) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, x, f)))⟫

@[simp] theorem sg_any_closed_l {d} (ω e b n m G u : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hb : b.freeSupport = [])
    (hn : n.freeSupport = []) (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (sg_any_m (𝒞 := 𝒞) ω e b n m G u).FreeClosed := by
  simp -implicitDefEqProofs [sg_any_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hw, he, hb, hn, hm, hG, hu]

theorem sg_any_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω e b n m G u : Term d) :
    Formula.satisfies ρ (sg_any_m (𝒞 := 𝒞) ω e b n m G u) ↔
      Sg_any_d I (ω.eval ρ) (e.eval ρ) (b.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [sg_any_m, Sg_any_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]
  rfl

theorem sg_any_build_l (hZF : M.Models ZF) {ω e b n : M.Domain}
    (hω : M.IsOmega ω) (hb : M.mem b ω) (hn : M.mem n ω) :
    ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_any_d I ω e b n m G u := by
  let ρ : Env M 3 := ⟨Fin.cases b (Fin.cases e (fun _ => ω)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := .existsE (.existsE (.existsE (.conj
    (sfm_m (𝒞 := 𝒞) (.bound 6) (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 2))
      (sg_any_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))) }
  have sat k : φ.denote ρ k ↔ ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_any_d I ω e b k m G u := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sfm_sat_l I hZF.1, Formula.satisfies_mem_iff, sg_any_sat_l I hZF.1]
    rfl
  apply (sat n).mp
  apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
  · intro z hz
    have empty : Sfm_d I ω z z := ⟨num_mem_l hZF.1 hω (show Num_d 0 z from hz),
      Structure.IsSequenceOfLength.empty I hz, fun _ _ h => h.elim fun p hp => (hz p hp.2).elim⟩
    obtain ⟨m, G, add, eq⟩ := sfm_eq_l I hZF hω empty hb hb
    obtain ⟨l, H, u, neg, read⟩ := sfm_neg_l I hZF hω add.program add.root
    refine (sat z).mpr ⟨l, H, u, neg.program, neg.root, fun X R E f x hE hf hx => ?_⟩
    exact (read X R E f hf).trans ((not_congr (eq X R E f x x hE hf hx hx)).trans
      (iff_of_false (fun h => h rfl) (fun ⟨i, hi, _⟩ => hz i hi)))
  · intro k hk ih l succ
    obtain ⟨m, G, u, prog, hu, all⟩ := (sat k).mp ih
    by_cases hke : k = e
    · refine (sat l).mpr ⟨m, G, u, prog, hu, fun X R E f x hE hf hx => (all X R E f x hE hf hx).trans ?_⟩
      exact ⟨fun ⟨i, hi, ne, hx⟩ => ⟨i, (succ i).mpr (Or.inl hi), ne, hx⟩,
        fun ⟨i, hi, ne, hx⟩ => ⟨i, ((succ i).mp hi).elim id
          (fun eq => (ne ((hZF.1.eq_of_same_members i k eq).trans hke)).elim), ne, hx⟩⟩
    obtain ⟨m₁, G₁, add, eq⟩ := sfm_eq_l I hZF hω prog hb hk
    obtain ⟨m₂, G₂, v, disj, both⟩ := sfm_or_l I hZF hω add.program (add.span u hu) add.root
    refine (sat l).mpr ⟨m₂, G₂, v, disj.program, disj.root, fun X R E f x hE hf hx => ?_⟩
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 k hk
    have old := (add.sat_l I hZF prog hu X R E f).symm.trans (all X R E f x hE hf hx)
    refine (both X R E f hf).trans ((or_congr old (eq X R E f x y hE hf hx hy)).trans ⟨?_, ?_⟩)
    · rintro (⟨i, hi, ne, hx⟩ | eq)
      · exact ⟨i, (succ i).mpr (Or.inl hi), ne, hx⟩
      · exact ⟨k, succ.predecessor_mem, hke, eq.symm ▸ hy⟩
    · rintro ⟨i, hi, ne, hx⟩
      rcases (succ i).mp hi with hi | eq
      · exact Or.inl ⟨i, hi, ne, hx⟩
      · exact Or.inr (((hE f).mp hf).1.2 k x y (hZF.1.eq_of_same_members i k eq ▸ hx) hy)

end YesMetaZFC.SetTheory.Internal

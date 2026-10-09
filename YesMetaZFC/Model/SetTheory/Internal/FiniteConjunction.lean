import YesMetaZFC.Model.SetTheory.Internal.InstructionAppend

/-! # 任意内部有限组变量的合取编译

沿内部 ω 实际追加成员指令及合取。归纳不变式使用可分离的满足关系公式，
输出仍是原合法程序；不把内部变量数换成宿主 Nat。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sg_all_d (ω b n m G u : M.Domain) : Prop := ∀ X R E f x,
  M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I b x f →
    (Ssat_d I X R E G m u f ↔ ∀ i y, M.mem i n → M.PairMember I i y f → M.PairMember I y x R)

def sg_all_m {d} (ω b n m G u : Term d) : Formula 1 d := set[d] ⟪∀ X R E f x,
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E, ⌜ω⌝ₛ, X) → f ∈ E → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ, x, f) →
  (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔
    (∀ i y, i ∈ ⌜n⌝ₛ → ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, y, f) → ⌜Formula.orderedPairMem 𝒞⌝ₚ(y, x, R)))⟫

@[simp] theorem sg_all_closed_l {d} (ω b n m G u : Term d)
    (hω : ω.freeSupport = []) (hb : b.freeSupport = []) (hn : n.freeSupport = [])
    (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (sg_all_m (𝒞 := 𝒞) ω b n m G u).FreeClosed := by
  simp -implicitDefEqProofs [sg_all_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hb, hn, hm, hG, hu]

theorem sg_all_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b n m G u : Term d) :
    Formula.satisfies ρ (sg_all_m (𝒞 := 𝒞) ω b n m G u) ↔
      Sg_all_d I (ω.eval ρ) (b.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [sg_all_m, Sg_all_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionSpace_iff I hE, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 自动编译所有 i<n 的关系断言 R(vᵢ,v_b)，允许内部非标准的 n。 -/
theorem sg_all_build_l (hZF : M.Models ZF) {ω b n : M.Domain}
    (hω : M.IsOmega ω) (hb : M.mem b ω) (hn : M.mem n ω) :
    ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_all_d I ω b n m G u := by
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => ω), fun _ => ω⟩
  let φ : UnarySchema 2 := { body := .existsE (.existsE (.existsE (.conj
    (sfm_m (𝒞 := 𝒞) (.bound 5) (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 2))
      (sg_all_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))) }
  have sat k : φ.denote ρ k ↔ ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Sg_all_d I ω b k m G u := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sfm_sat_l I hZF.1, Formula.satisfies_mem_iff, sg_all_sat_l I hZF.1]; rfl
  apply (sat n).mp
  apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
  · intro e he
    have empty : Sfm_d I ω e e := ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he),
      Structure.IsSequenceOfLength.empty I he, fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
    obtain ⟨m, G, built, read⟩ := sfm_eq_l I hZF hω empty hb hb
    refine (sat e).mpr ⟨m, G, e, built.program, built.root, fun X R E f x hE hf hbx => ?_⟩
    exact (read X R E f x x hE hf hbx hbx).trans ⟨fun _ i _ hi => (he i hi).elim, fun _ => rfl⟩
  · intro k hk ih l succ
    obtain ⟨m, G, u, hG, hu, all⟩ := (sat k).mp ih
    obtain ⟨m₁, G₁, add, read⟩ := sfm_rel_l I hZF hω hG hk hb
    obtain ⟨m₂, G₂, v, conj, both⟩ := sfm_and_l I hZF hω add.program (add.span u hu) add.root
    refine (sat l).mpr ⟨m₂, G₂, v, conj.program, conj.root, fun X R E f x hE hf hbx => ?_⟩
    obtain ⟨y, hy, hky⟩ := ((hE f).mp hf).2.2 k hk
    have old := (add.sat_l I hZF hG hu X R E f).symm.trans (all X R E f x hE hf hbx)
    refine (both X R E f hf).trans ((and_congr old (read X R E f y x hE hf hky hbx)).trans ⟨?_, ?_⟩)
    · rintro ⟨prev, last⟩ i z hi hiz
      rcases (succ i).mp hi with hi | hi
      · exact prev i z hi hiz
      · have eq := hZF.1.eq_of_same_members i k hi
        subst i
        exact ((hE f).mp hf).1.2 k z y hiz hky ▸ last
    · intro full
      exact ⟨fun i z hi hiz => full i z ((succ i).mpr (Or.inl hi)) hiz, full k y succ.predecessor_mem hky⟩

end YesMetaZFC.SetTheory.Internal

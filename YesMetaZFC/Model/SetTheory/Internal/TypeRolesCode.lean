import YesMetaZFC.Model.SetTheory.Internal.TypeRolesSyntax
import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 任意内部有限组标签角色的实际编译

首个标签检查为零，随后检查相邻标签互为后继。内部 ω 归纳证明所得单一
程序恰为所有 i<k 的标签约束；不使用外部标准性或额外的自然数常量列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_prog_d (ω k m G u : M.Domain) : Prop := ∀ c X R E f,
  Smem_d I c X R → M.TransitiveSet X → M.IsFunctionSpace I E ω X → M.mem f E →
    (Ssat_d I X R E G m u f ↔ Tr_roles_d I k f)

def tr_prog_m {d} (ω k m G u : Term d) : Formula 1 d := set[d] ⟪∀ c X R E f,
  ⌜smem_m (𝒞 := 𝒞)⌝ₚ(c, X, R) → ⌜Formula.isTransitive⌝ₚ(X) →
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E, ⌜ω⌝ₛ, X) → f ∈ E →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔ ⌜tr_roles_m (𝒞 := 𝒞)⌝ₚ(⌜k⌝ₛ, f))⟫

@[simp] theorem tr_prog_closed_l {d} (ω k m G u : Term d)
    (hω : ω.freeSupport = []) (hk : k.freeSupport = []) (hm : m.freeSupport = [])
    (hG : G.freeSupport = []) (hu : u.freeSupport = []) : (tr_prog_m (𝒞 := 𝒞) ω k m G u).FreeClosed := by
  simp -implicitDefEqProofs [tr_prog_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hk, hm, hG, hu]

theorem tr_prog_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω k m G u : Term d) :
    Formula.satisfies ρ (tr_prog_m (𝒞 := 𝒞) ω k m G u) ↔
      Tr_prog_d I (ω.eval ρ) (k.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [tr_prog_m, Tr_prog_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    smem_sat_l I, Formula.satisfies_isTransitive_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, ssat_sat_l I hE, tr_roles_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

theorem tr_roles_build_l (hZF : M.Models ZF) {ω k : M.Domain} (hω : M.IsOmega ω) (hk : M.mem k ω) :
    ∃ a m G u, Sformula_d I ω a m G u ∧ ∀ c X R f,
      Smem_d I c X R → M.TransitiveSet X → M.IsSetFunctionFromTo I f ω X →
        (Satisfies_d I ω c a f ↔ Tr_roles_d I k f) := by
  -- 内部自然数的零／后继分类用于选择固定语法模板，不枚举外部自然数。
  obtain ⟨Ω, hΩ, finite⟩ := KPi.exists_omega_l (ZF.models_kpi_l hZF)
  have eq := hZF.1.eq_of_same_members Ω ω (fun x => ⟨hΩ.2 ω hω.1 x, hω.2 Ω hΩ.1 x⟩)
  subst Ω
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.existsE (.conj
    (sfm_m (𝒞 := 𝒞) (.bound 4) (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 2))
      (tr_prog_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))) }
  have sat n : φ.denote ρ n ↔ ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ Tr_prog_d I ω n m G u := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sfm_sat_l I hZF.1, Formula.satisfies_mem_iff, tr_prog_sat_l I hZF.1]; rfl
  have built : φ.denote ρ k := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ k hk
    · intro e he
      have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
      have empty : Sfm_d I ω e e := ⟨heω, Structure.IsSequenceOfLength.empty I he,
        fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
      obtain ⟨m, G, add, read⟩ := sfm_eq_l I hZF hω empty heω heω
      refine (sat e).mpr ⟨m, G, e, add.program, add.root, fun c X R E f _ _ hE hf => ?_⟩
      obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 e heω
      exact (read X R E f x x hE hf hx hx).trans
        ⟨fun _ i _ _ hi => (he i hi).elim, fun _ => rfl⟩
    · intro n hn ih l hl
      obtain ⟨m, G, u, hG, hu, all⟩ := (sat n).mp ih
      have hlω : M.mem l ω := by
        obtain ⟨l', hl', mem⟩ := hω.1.2 n hn
        exact (hl'.eq hZF.1 hl) ▸ mem
      obtain ⟨b, hb, hbω⟩ := hω.1.2 l hlω
      -- 已有前缀固定第 n 项的标签；新检查只需读取相邻两个坐标。
      have test : ∃ ψ : Formula 1 2, ψ.FreeClosed ∧ ψ.IsDelta0 ∧ ∀ f p q,
          Tr_roles_d I n f → M.PairMember I n p f →
            (Formula.satisfies (⟨Fin.cases q (fun _ => p), fun _ => q⟩ : Env M 2) ψ ↔ Tr_tag_d n q) := by
        rcases ((finite n).mp hn).2.1 with zero | ⟨j, hj, succ⟩
        · exact ⟨tr_zero_m .newest, tr_zero_m_freeClosed _ rfl, tr_zero_delta_l _, fun _ _ q _ _ =>
            (tr_zero_sat_l hZF.1 _ _).trans (tr_zero_iff_l hZF.1 zero)⟩
        · exact ⟨tr_step_m (.bound 1) .newest, tr_step_m_freeClosed _ _ rfl rfl, tr_step_delta_l _ _,
            fun f p q roles hp => (tr_step_sat_l hZF.1 _ _ _).trans
              (tr_step_iff_l hZF.1 (roles j n p hj succ hp) succ)⟩
      obtain ⟨ψ, closed, delta, test⟩ := test
      obtain ⟨m₁, G₁, v, add, compile⟩ := source_compile_core_l I hZF hω (source_core_l ψ)
        (source_core_closed_l ψ closed) (Fin.cases l (fun _ => n)) hbω
        (Fin.cases hb.predecessor_mem (fun _ => (hb n).mpr (Or.inl hl.predecessor_mem))) hG
      obtain ⟨m₂, G₂, w, conj, both⟩ := sfm_and_l I hZF hω add.program (add.span u hu) add.root
      refine (sat l).mpr ⟨m₂, G₂, w, conj.program, conj.root, fun c X R E f model trans hE hf => ?_⟩
      have fn := (hE f).mp hf
      obtain ⟨p, hpX, hp⟩ := fn.2.2 n hn
      obtain ⟨q, hqX, hq⟩ := fn.2.2 l hlω
      let η : Env (smdl_structure_l I (R := R) model.1.2.1) 2 :=
        ⟨Fin.cases ⟨q, hqX⟩ (fun _ => ⟨p, hpX⟩), fun _ => ⟨q, hqX⟩⟩
      have atom := (compile X R model.1.2.1 E hE f hf η (Fin.cases hq (fun _ => hp))).trans
        ((source_core_sat_l ψ η).trans (smem_delta_image_l I model trans delta η))
      have env : image_env_l Subtype.val η = (⟨Fin.cases q (fun _ => p), fun _ => q⟩ : Env M 2) := by
        change Env.mk _ _ = Env.mk _ _
        congr 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [env] at atom
      have old := (add.sat_l I hZF hG hu X R E f).symm.trans (all c X R E f model trans hE hf)
      exact (both X R E f hf).trans ((and_congr old atom).trans
        ((and_congr_right fun prev => test f p q prev hp).trans (tr_roles_last_l I hZF.1 hl fn.1 hq).symm))
  obtain ⟨m, G, u, hG, hu, all⟩ := (sat k).mp built
  obtain ⟨a, ha⟩ := I.total G u
  have form : Sformula_d I ω a m G u := ⟨ha, hG, hu⟩
  refine ⟨a, m, G, u, form, fun c X R f model trans fn => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  exact (satisfies_decode_l I hZF.1 model.1 form hE).trans (all c X R E f model trans hE ((hE f).mpr fn))

end YesMetaZFC.SetTheory.Internal

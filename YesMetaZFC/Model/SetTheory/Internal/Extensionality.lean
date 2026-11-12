import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Embedding.Range
import YesMetaZFC.SetTheory.Collapse.RelationIso

/-! # 内部等号与外延性的保持

先编译成员一致，再接真正的等号指令与两个全称量词。这个内部句子的真值
恰好是关系外延性，故可以沿任意完整内部初等嵌入送到目标结构。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sext_code_l {ω : M.Domain} (hω : M.IsOmega ω) : ∃ n F k,
    Sfm_d I ω n F ∧ M.mem k n ∧ ∀ X R E f, (∃ x, M.mem x X) →
      M.IsFunctionSpace I E ω X → M.mem f E → (Ssat_d I X R E F n k f ↔ Wc_ext_d X R) := by
  let φ : Formula 1 2 := Formula.extensionalEq (.bound 0) (.bound 1)
  obtain ⟨_, n, F, k, v, prog, hv, sem⟩ := source_compile_l I hZF hω φ (by simp [φ])
  have hi i := num_mem_l hZF.1 hω (hv i)
  have ne : v 0 ≠ v 1 := fun h => by
    have := num_injective_l (ZF.modelsKP hZF) (hv 0) (h.symm ▸ hv 1)
    contradiction
  obtain ⟨m, G, eq, eqs⟩ := sfm_eq_l I hZF hω prog.2.1 (hi 0) (hi 1)
  obtain ⟨l, H, r, imp, imps⟩ := sfm_imp_l I hZF hω eq.program (eq.span k prog.2.2) eq.root
  have matrix X R E f (hX : ∃ x, M.mem x X) (hE : M.IsFunctionSpace I E ω X) (hf : M.mem f E)
      x y (hx : M.mem x X) (hy : M.mem y X) (hfx : Rd_entry_d (v 0) x f) (hfy : Rd_entry_d (v 1) y f) :
      Ssat_d I X R E H l r f ↔ ((∀ z, M.mem z X → (Rd_entry_d z x R ↔ Rd_entry_d z y R)) → x = y) := by
    let ρ : Env (smdl_structure_l I (R := R) hX) 2 := ⟨Fin.cases ⟨x, hx⟩ (fun _ => ⟨y, hy⟩), fun _ => ⟨x, hx⟩⟩
    have hp i : M.PairMember I (v i) (ρ.bound i).val f := by
      refine Fin.cases hfx (fun j => ?_) i
      have e : j = 0 := Fin.ext (by omega)
      exact e ▸ hfy
    have hs := sem X R hX E hE f hf ρ hp
    have read : Formula.satisfies ρ φ ↔ ∀ z, M.mem z X → (Rd_entry_d z x R ↔ Rd_entry_d z y R) :=
      (Formula.satisfies_extensionalEq_iff ρ _ _).trans
        ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z.val z.property⟩
    exact (imps X R E f hf).trans (imp_congr ((eq.sat_l I hZF prog.2.1 prog.2.2 X R E f).symm.trans
      (hs.trans read)) (eqs X R E f x y hE hf hfx hfy))
  obtain ⟨s, J, t, all₁, s₁⟩ := sfm_all_l I hZF hω imp.program (hi 1) imp.root
  obtain ⟨u, K, w, all₀, s₀⟩ := sfm_all_l I hZF hω all₁.program (hi 0) all₁.root
  refine ⟨u, K, w, all₀.program, all₀.root, fun X R E f hX hE hf => ?_⟩
  have at₀ x g (h : Senv_update_d I f (v 0) x g) : Rd_entry_d (v 0) x g := (h.2 _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  rw [s₀ X R E f hE hf]
  constructor
  · intro h x hx y hy same
    obtain ⟨g, hg, hgf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hi 0) hx
    obtain ⟨e, he, _⟩ := senv_update_exists_l I hZF hgf (hi 1) hy
    have hs := (s₁ X R E g hE ((hE g).mpr hgf)).mp (h x g hx hg) y e hy he
    exact (matrix X R E e hX hE ((hE e).mpr (he.function_l I hgf (hi 1) hy)) x y hx hy
      ((he.2 _ _).mpr (Or.inr ⟨ne, at₀ x g hg⟩)) ((he.2 _ _).mpr (Or.inl ⟨rfl, rfl⟩))).mp hs same
  · intro h x g hx hg
    have hgf := hg.function_l I ((hE f).mp hf) (hi 0) hx
    apply (s₁ X R E g hE ((hE g).mpr hgf)).mpr
    intro y e hy he
    exact (matrix X R E e hX hE ((hE e).mpr (he.function_l I hgf (hi 1) hy)) x y hx hy
      ((he.2 _ _).mpr (Or.inr ⟨ne, at₀ x g hg⟩)) ((he.2 _ _).mpr (Or.inl ⟨rfl, rfl⟩))).mpr (h x hx y hy)

theorem Smap_d.extensional_l {ω c d X R Y S j : M.Domain} (hω : M.IsOmega ω)
    (hc : Smdl_d I c X R) (hd : Smdl_d I d Y S) (h : Smap_d I ω c d X Y j)
    (he : Wc_ext_d X R) : Wc_ext_d Y S := by
  obtain ⟨n, F, k, hp, hk, spec⟩ := sext_code_l hZF hω
  obtain ⟨E, hE, f, hf⟩ := senv_space_l I hZF ω hc.2.1
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF h.1.1 ((hE f).mp hf)
  exact (spec Y S K g hd.2.1 hK ((hK g).mpr hg)).mp
    ((h.ssat_l I hZF.1 hc hd hp hk hE hK hf ((hK g).mpr hg) hfg).mp ((spec X R E f hc.2.1 hE hf).mpr he))

end YesMetaZFC.SetTheory.Internal

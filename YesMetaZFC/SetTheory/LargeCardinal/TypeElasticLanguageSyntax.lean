import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticProgramSyntax

/-! # 弹性语言证书的原公式

代码表的一行保留原四条查询及所有实际读取性质。对该原公式作集合内
选择，得到的仍是原来的 `Ee_language_d`，没有额外语义参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ee_successor_m {d} (ω n U D g : Term d) : Formula 1 d := set[d] ⟪∀ μ Y c R s δ t,
  ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
    (⌜g⌝ₛ ∈ t ↔ ∃ ν, ⌜Formula.isSuccessor⌝ₚ(μ, ν))⟫
derive_free_closed ee_successor_m

def ee_domain_m {d} (ω κ n U D h : Term d) : Formula 1 d := set[d] ⟪∀ ν μ A Y c R s δ t,
  ⌜v_m kpair_convention_l⌝ₚ(ν, A) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜Formula.isSuccessor⌝ₚ(μ, ν) →
  ⌜ω⌝ₛ ⊆ ν → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
    (⌜h⌝ₛ ∈ t ↔ ⌜fn0_m⌝ₚ(⌜n⌝ₛ, A, s) ∧ δ ∈ A ∧ ⌜κ⌝ₛ ∈ A)⟫
derive_free_closed ee_domain_m

def ee_inacc_m {d} (ω n U D i : Term d) : Formula 1 d := set[d] ⟪∀ c Y R s δ t,
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
    (⌜i⌝ₛ ∈ t ↔ ⌜sc_inaccessible_raw_m⌝ₚ(⌜ω⌝ₛ, Y, δ))⟫
derive_free_closed ee_inacc_m

def ee_domain_pack0_m : Formula 1 7 :=
  let ω := Term.bound 0; let κ := Term.bound 1; let n := Term.bound 2
  let U := Term.bound 3; let D := Term.bound 4; let g := Term.bound 5; let h := Term.bound 6
  set[7] ⟪
  ⌜ω⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ) ∧
  ⌜ee_successor_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g⌝ₛ) ∧
  ⌜ee_domain_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜h⌝ₛ)⟫

theorem ee_domain_pack0_closed_l : ee_domain_pack0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_domain_pack0_m, Definitional.Formula.FreeClosed]

def ee_domain_pack_m {d} (ω κ n U D g h : Term d) : Formula 1 d :=
  ee_domain_pack0_m.bind (fun i => [ω, κ, n, U, D, g, h].get i)

@[simp] theorem ee_domain_pack_closed_l {d} (ω κ n U D g h : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : n.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hg : g.freeSupport = []) (hh : h.freeSupport = []) :
    (ee_domain_pack_m ω κ n U D g h).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ee_domain_pack0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hk, hn, hU, hD, hg, hh, fun i => Fin.elim0 i⟩

theorem ee_domain_pack_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω κ n U D g h : Term d) :
    Formula.satisfies ρ (ee_domain_pack_m ω κ n U D g h) ↔
      Ee_domain_d hZF (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (g.eval ρ) (h.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ee_domain_pack_m, Formula.satisfies_bind, ee_domain_pack0_m, ee_successor_m, ee_domain_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, tt_pool_sat_l I (ZF.modelsKP hZF), Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hZF.1, smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, fn0_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun p => ⟨p.omega_mem, p.pool, p.successor, p.domain⟩⟩

def ee_language0_m : Formula 1 10 :=
  let ω := Term.bound 0; let κ := Term.bound 1; let n := Term.bound 2
  let B := Term.bound 3; let U := Term.bound 4; let D := Term.bound 5
  let g := Term.bound 6; let h := Term.bound 7; let i := Term.bound 8; let e := Term.bound 9
  set[10] ⟪
  ⌜ee_domain_pack_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g⌝ₛ, ⌜h⌝ₛ) ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜κ⌝ₛ) ∧ ⌜v_sigma_m⌝ₚ(⌜κ⌝ₛ, ⌜B⌝ₛ) ∧
  ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, ⌜B⌝ₛ, ⌜U⌝ₛ) ∧
  ⌜g⌝ₛ ∈ ⌜D⌝ₛ ∧ ⌜h⌝ₛ ∈ ⌜D⌝ₛ ∧ ⌜i⌝ₛ ∈ ⌜D⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜D⌝ₛ ∧
  ⌜ee_inacc_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜i⌝ₛ) ∧
  ⌜ee_read_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ) ∧
  ⌜ee_numeric_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ)⟫
@[simp] theorem ee_language0_closed_l : ee_language0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_language0_m, Definitional.Formula.FreeClosed]

def ee_language_m {d} (ω κ n B U D g h i e : Term d) : Formula 1 d :=
  ee_language0_m.bind (fun j => [ω, κ, n, B, U, D, g, h, i, e].get j)

@[simp] theorem ee_language_closed_l {d} (ω κ n B U D g h i e : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : n.freeSupport = [])
    (hB : B.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hg : g.freeSupport = []) (hh : h.freeSupport = []) (hi : i.freeSupport = []) (he : e.freeSupport = []) :
    (ee_language_m ω κ n B U D g h i e).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ee_language0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hk, hn, hB, hU, hD, hg, hh, hi, he, fun j => Fin.elim0 j⟩

theorem ee_language0_sat_l (hZFC : M.Models ZFC) (ρ : Env M 10) :
    Formula.satisfies ρ ee_language0_m ↔
      Ee_language_d (ZFC.models_zf_l hZFC) (ρ.bound 0) (ρ.bound 1) (ρ.bound 2)
        (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) ⟨ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9⟩ := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ee_language0_m, ee_inacc_m, ee_domain_pack_sat_l hZF,
    Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    sc_inaccessible_raw_sat_l, ee_read_sat_l hZF, ee_numeric_sat_l hZFC, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨a, b, c, d, f, j, k, l, v, r, numeric⟩
    exact ⟨a, b, c, d, f, j, k, l, v, fun _ => r, numeric⟩
  · intro q
    exact ⟨q.toEe_domain_d, q.limit, q.rank, q.constants, q.largest_mem, q.domain_mem, q.inaccessible_mem,
      q.stretch_mem, q.inaccessible, q.read hZFC, q.numeric⟩

theorem ee_language_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω κ n B U D g h i e : Term d) :
    Formula.satisfies ρ (ee_language_m ω κ n B U D g h i e) ↔
      Ee_language_d (ZFC.models_zf_l hZFC) (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ := by
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_sat_l hZFC]
  rfl

def ee_rebuild_seed_m : Formula 1 10 :=
  let p : Fin 10 → Term 10 := Term.bound
  set[10] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 1⌝ₛ) ∧
    ⌜v_sigma_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 3⌝ₛ) ∧ ⌜tt_constants0_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ) ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ) ∧ ⌜p 9⌝ₛ ∈ ⌜p 5⌝ₛ ∧
    ⌜ee_numeric_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 4⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ)⟫

@[simp] theorem ee_rebuild_seed_closed_l : ee_rebuild_seed_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_rebuild_seed_m, Definitional.Formula.FreeClosed]

def ee_rebuild_m : Formula 1 0 := Formula.forallClosure 10 (.imp ee_rebuild_seed_m ee_language0_m)

theorem ee_rebuild_closed_l : ee_rebuild_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨ee_rebuild_seed_closed_l, ee_language0_closed_l⟩

/-- 目标秩段只需反射这条已证重建句子，无须满足整个 ZFC。 -/
theorem ee_rebuild_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) ee_rebuild_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [Formula.satisfies_imp_iff, ee_rebuild_seed_m, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF), Formula.satisfies_mem_iff,
    ee_numeric_sat_l hZFC, ee_language0_sat_l hZFC]
  rintro ⟨hw, hk, rank, constants, pool, he, numeric⟩
  exact numeric.language_l hZF hw hk rank constants pool he

end YesMetaZFC.SetTheory.LargeCardinal

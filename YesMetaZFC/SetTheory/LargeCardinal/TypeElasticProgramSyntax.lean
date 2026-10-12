import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticReadSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeProgramSyntax

/-! # 弹性程序的低参数正确性句子

四个程序只携带 ω、内部元数和自然数码；原 κ 常量留在实际名字列中。
因此程序正确性可沿固定低参数的根嵌入往返，而不会假定语义证书绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ee_largest_program0_m : Formula 1 2 :=
  let ω : Term 2 := .bound 0
  let z : Term 2 := .bound 1
  set[2] ⟪⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∀ n U D p, ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, n, U, D) → ⌜tt_code0_m⌝ₚ(n, U, ⌜z⌝ₛ, p) → p ∈ D ∧
    (∀ μ Y c R s δ t, ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
      ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, n, s, δ, U, D, t) →
        (p ∈ t ↔ ∃ ν, ⌜Formula.isSuccessor⌝ₚ(μ, ν))))⟫
theorem ee_largest_program0_closed_l : ee_largest_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_largest_program0_m, Definitional.Formula.FreeClosed]

def ee_largest_program_m {d} (ω z : Term d) : Formula 1 d :=
  ee_largest_program0_m.bind (Fin.cases ω (fun _ => z))

@[simp] theorem ee_largest_program_closed_l {d} (ω z : Term d)
    (hw : ω.freeSupport = []) (hz : z.freeSupport = []) : (ee_largest_program_m ω z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hw (fun _ => hz)) _).mpr ee_largest_program0_closed_l

def ee_inacc_program0_m : Formula 1 2 :=
  let ω : Term 2 := .bound 0
  let z : Term 2 := .bound 1
  set[2] ⟪⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∀ n U D kw p, ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, n, U, D) → ⌜ω⌝ₛ ∈ U → ⌜kpair0_m⌝ₚ(kw, ⌜ω⌝ₛ, ⌜ω⌝ₛ) →
    ⌜tt_code2_m⌝ₚ(n, U, ⌜z⌝ₛ, p, n, kw) → p ∈ D ∧
    (∀ c Y R s δ t, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
      ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, n, s, δ, U, D, t) →
        (p ∈ t ↔ ⌜sc_inaccessible_raw_m⌝ₚ(⌜ω⌝ₛ, Y, δ))))⟫
theorem ee_inacc_program0_closed_l : ee_inacc_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_inacc_program0_m, Definitional.Formula.FreeClosed]

def ee_inacc_program_m {d} (ω z : Term d) : Formula 1 d :=
  ee_inacc_program0_m.bind (Fin.cases ω (fun _ => z))

@[simp] theorem ee_inacc_program_closed_l {d} (ω z : Term d)
    (hw : ω.freeSupport = []) (hz : z.freeSupport = []) : (ee_inacc_program_m ω z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hw (fun _ => hz)) _).mpr ee_inacc_program0_closed_l

def ee_stretch_code_m {d} (ω n κ v d₀ e z p : Term d) : Formula 1 d := set[d] ⟪∃ C kw kn kk,
  ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C) ∧ ⌜kpair0_m⌝ₚ(kw, ⌜ω⌝ₛ, ⌜ω⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(kn, ⌜n⌝ₛ, ⌜n⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(kk, ⌜κ⌝ₛ, ⌜κ⌝ₛ) ∧
  (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧ ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, kw, C) ∧
  ⌜rd_entry0_m⌝ₚ(⌜v⌝ₛ, kn, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜d₀⌝ₛ, ⌜n⌝ₛ, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, kk, C)⟫
derive_free_closed ee_stretch_code_m

def ee_stretch_read_m {d} (ω n v d₀ e z : Term d) : Formula 1 d := set[d] ⟪∀ ν μ X Y Z c R c' R' κ δ K S s f,
  ⌜v_m kpair_convention_l⌝ₚ(ν, X) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜Formula.isSuccessor⌝ₚ(μ, ν) →
  ⌜v_m kpair_convention_l⌝ₚ(δ, Z) → ⌜Formula.isLimitOrdinal⌝ₚ(δ) → ⌜ω⌝ₛ ∈ δ → κ ∈ δ →
  ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, κ, K, Z, S) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c', Y, R') → ⌜fn0_m⌝ₚ(⌜n⌝ₛ, X, s) → δ ∈ X →
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f, ⌜ω⌝ₛ, Y) →
  (∀ i x, i ∈ ⌜n⌝ₛ → (⌜rd_entry0_m⌝ₚ(i, x, s) ↔ ⌜rd_entry0_m⌝ₚ(i, x, f))) →
  ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, ⌜ω⌝ₛ, f) → ⌜rd_entry0_m⌝ₚ(⌜v⌝ₛ, ⌜n⌝ₛ, f) →
  ⌜rd_entry0_m⌝ₚ(⌜d₀⌝ₛ, δ, f) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, κ, f) →
    (⌜sc_sat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c', ⌜z⌝ₛ, f) ↔
      ⌜ee_realized0_m⌝ₚ(⌜ω⌝ₛ, κ, δ, ⌜n⌝ₛ, s, c, Z, S))⟫
derive_free_closed ee_stretch_read_m

def ee_stretch_program0_m : Formula 1 6 :=
  let ω : Term 6 := .bound 0
  let n : Term 6 := .bound 1
  let v : Term 6 := .bound 2
  let d₀ : Term 6 := .bound 3
  let e : Term 6 := .bound 4
  let z : Term 6 := .bound 5
  set[6] ⟪
  ⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜d₀⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜v⌝ₛ, ⌜n⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜d₀⌝ₛ, ⌜v⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜e⌝ₛ, ⌜d₀⌝ₛ) ∧ ⌜ee_stretch_read_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜v⌝ₛ, ⌜d₀⌝ₛ, ⌜e⌝ₛ, ⌜z⌝ₛ)⟫
theorem ee_stretch_program0_closed_l : ee_stretch_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_stretch_program0_m, Definitional.Formula.FreeClosed]

def ee_stretch_program_m {d} (ω n v d₀ e z : Term d) : Formula 1 d :=
  ee_stretch_program0_m.bind (Fin.cases ω (Fin.cases n (Fin.cases v (Fin.cases d₀ (Fin.cases e (fun _ => z))))))

@[simp] theorem ee_stretch_program_closed_l {d} (ω n v d₀ e z : Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hv : v.freeSupport = [])
    (hd : d₀.freeSupport = []) (he : e.freeSupport = []) (hz : z.freeSupport = []) :
    (ee_stretch_program_m ω n v d₀ e z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hn (Fin.cases hv (Fin.cases hd (Fin.cases he (fun _ => hz)))))) _).mpr ee_stretch_program0_closed_l

def ee_numeric0_m : Formula 1 8 :=
  let p : Fin 8 → Term 8 := Term.bound
  set[8] ⟪∃ l v d e zg zh zi ze kw,
    ⌜ee_largest_program_m⌝ₚ(⌜p 0⌝ₛ, zg) ∧ ⌜tt_code0_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 3⌝ₛ, zg, ⌜p 4⌝ₛ) ∧
    ⌜tg_guard_program_m⌝ₚ(⌜p 0⌝ₛ, l, zh) ∧ ⌜tg_guard_code_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, l, zh, ⌜p 5⌝ₛ) ∧
    ⌜ee_inacc_program_m⌝ₚ(⌜p 0⌝ₛ, zi) ∧ ⌜kpair0_m⌝ₚ(kw, ⌜p 0⌝ₛ, ⌜p 0⌝ₛ) ∧
    ⌜tt_code2_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 3⌝ₛ, zi, ⌜p 6⌝ₛ, ⌜p 2⌝ₛ, kw) ∧
    ⌜ee_stretch_program_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, v, d, e, ze) ∧
    ⌜ee_stretch_code_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 1⌝ₛ, v, d, e, ze, ⌜p 7⌝ₛ)⟫

theorem ee_numeric0_closed_l : ee_numeric0_m.FreeClosed := by
  simp -implicitDefEqProofs [ee_numeric0_m, Definitional.Formula.FreeClosed]

def ee_numeric_m {d} (ω κ n U g h i j : Term d) : Formula 1 d := ee_numeric0_m.bind
  (Fin.cases ω (Fin.cases κ (Fin.cases n (Fin.cases U (Fin.cases g (Fin.cases h (Fin.cases i (fun _ => j))))))))

@[simp] theorem ee_numeric_closed_l {d} (ω κ n U g h i j : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : n.freeSupport = []) (hU : U.freeSupport = [])
    (hg : g.freeSupport = []) (hh : h.freeSupport = []) (hi : i.freeSupport = []) (hj : j.freeSupport = []) :
    (ee_numeric_m ω κ n U g h i j).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hk (Fin.cases hn (Fin.cases hU (Fin.cases hg (Fin.cases hh (Fin.cases hi (fun _ => hj)))))))) _).mpr
      ee_numeric0_closed_l

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ee_largest_program_sat_l {d} (ρ : Env M d) (ω z : Term d) :
    Formula.satisfies ρ (ee_largest_program_m ω z) ↔ Ee_largest_program_d hZF (ω.eval ρ) (z.eval ρ) := by
  simp only [ee_largest_program_m, Formula.satisfies_bind, ee_largest_program0_m, Ee_largest_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, tt_pool_sat_l I (ZF.modelsKP hZF), tt_code0_sat_l (ZF.modelsKP hZF),
    v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]
  rfl

theorem ee_inacc_program_sat_l {d} (ρ : Env M d) (ω z : Term d) :
    Formula.satisfies ρ (ee_inacc_program_m ω z) ↔ Ee_inacc_program_d hZF (ω.eval ρ) (z.eval ρ) := by
  simp only [ee_inacc_program_m, Formula.satisfies_bind, ee_inacc_program0_m, Ee_inacc_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, tt_pool_sat_l I (ZF.modelsKP hZF), kpair0_sat_l hZF.1,
    tt_code2_sat_l (ZF.modelsKP hZF), smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_iff_iff,
    sc_inaccessible_raw_sat_l, Definitional.Term.eval_weaken]
  rfl

theorem ee_stretch_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n κ v d₀ e z p : Term d) :
    Formula.satisfies ρ (ee_stretch_code_m ω n κ v d₀ e z p) ↔
      Ee_stretch_code_d (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (v.eval ρ) (d₀.eval ρ) (e.eval ρ) (z.eval ρ) (p.eval ρ) := by
  simp only [ee_stretch_code_m, Ee_stretch_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem ee_stretch_read_sat_l {d} (ρ : Env M d) (ω n v d₀ e z : Term d) :
    Formula.satisfies ρ (ee_stretch_read_m ω n v d₀ e z) ↔
      Ee_stretch_read_d hZF (ω.eval ρ) (n.eval ρ) (v.eval ρ) (d₀.eval ρ) (e.eval ρ) (z.eval ρ) := by
  simp only [ee_stretch_read_m, Ee_stretch_read_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l I hZF.1, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff, ep_source_sat_l hZF, smem_sat_l I, fn0_sat_l hZF.1,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hZF.1, sc_sat_formula_l I hZF.1, Definitional.Term.eval_weaken]
  refine forall_congr' fun ν => forall_congr' fun μ => forall_congr' fun X => forall_congr' fun Y =>
    forall_congr' fun Z => forall_congr' fun c => forall_congr' fun R => forall_congr' fun c' =>
    forall_congr' fun R' => forall_congr' fun κ => forall_congr' fun δ => forall_congr' fun K =>
    forall_congr' fun S => forall_congr' fun s => forall_congr' fun f => ?_
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun source => ?_
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => iff_congr Iff.rfl ?_
  let θ := ρ.push ν |>.push μ |>.push X |>.push Y |>.push Z |>.push c |>.push R |>.push c'
    |>.push R' |>.push κ |>.push δ |>.push K |>.push S |>.push s |>.push f
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have read := ee_realized0_sat_l hZF θ (w ω) Term.newest.weaken.weaken.weaken.weaken.weaken
    Term.newest.weaken.weaken.weaken.weaken (w n) Term.newest.weaken
    Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
    Term.newest.weaken.weaken
    (by simpa only [θ, w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using source)
  simpa only [θ, w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using read

theorem ee_stretch_program_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω n v d₀ e z : Term d) :
    Formula.satisfies ρ (ee_stretch_program_m ω n v d₀ e z) ↔
      Ee_stretch_program_d (ω.eval ρ) (n.eval ρ) (v.eval ρ) (d₀.eval ρ) (e.eval ρ) (z.eval ρ) := by
  simp only [ee_stretch_program_m, Formula.satisfies_bind, ee_stretch_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, ee_stretch_read_sat_l (ZFC.models_zf_l hZFC)]
  exact ⟨fun ⟨hn, hv, hd, he, hz, sn, sv, sd, read⟩ => ⟨hn, hv, hd, he, hz, sn, sv, sd, fun _ => read⟩,
    fun p => ⟨p.finite, p.next_finite, p.point_finite, p.critical_finite, p.natural, p.next, p.point, p.critical, p.read hZFC⟩⟩

theorem ee_numeric_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω κ n U g h i j : Term d) :
    Formula.satisfies ρ (ee_numeric_m ω κ n U g h i j) ↔
      Ee_numeric_d (ZFC.models_zf_l hZFC) (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, j.eval ρ⟩ := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [ee_numeric_m, Formula.satisfies_bind, ee_numeric0_m, Ee_numeric_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ee_largest_program_sat_l hZF, tt_code0_sat_l (ZF.modelsKP hZF), tg_guard_program_sat_l (ZF.modelsKP hZF), tg_guard_code_sat_l (ZF.modelsKP hZF),
    ee_inacc_program_sat_l hZF, kpair0_sat_l hZF.1, tt_code2_sat_l (ZF.modelsKP hZF),
    ee_stretch_program_sat_l hZFC, ee_stretch_code_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

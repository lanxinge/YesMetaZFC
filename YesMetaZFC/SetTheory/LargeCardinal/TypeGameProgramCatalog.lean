import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticCatalog
import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramSyntax

/-! # 只按元数固定的子类型程序表

程序包只存自然数长度、七个自然数槽位和自然数程序码。整张函数图包含于
Vω，κ、较低域及候选类型不参与程序选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_program_packet_d (hZF : M.Models ZF) (ω n r : M.Domain) : Prop :=
  ∃ b z p q s₀ s₁ s₂ s₃ s₄ s₅ s₆ a,
    Rd_quad_d r b z p q ∧ Rd_quad_d p s₀ s₁ s₂ s₃ ∧ Rd_triple_d q s₄ s₅ s₆ ∧
    Ts_program_d hZF ω n b (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂
      (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) a z

def tg_program_packet_m {d} (ω n r : Term d) : Formula 1 d := set[d] ⟪∃ b z p q s₀ s₁ s₂ s₃ s₄ s₅ s₆ a,
  ⌜rd_quad_m⌝ₚ(⌜r⌝ₛ, b, z, p, q) ∧ ⌜rd_quad_m⌝ₚ(p, s₀, s₁, s₂, s₃) ∧ ⌜rd_triple0_m⌝ₚ(q, s₄, s₅, s₆) ∧
  ⌜fun ω n b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω n b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜ω⌝ₛ, ⌜n⌝ₛ, b, a, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆)⟫
@[simp] theorem tg_program_packet_closed_l {d} (ω n r : Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hr : r.freeSupport = []) :
    (tg_program_packet_m ω n r).FreeClosed := by
  simp -implicitDefEqProofs [tg_program_packet_m, Definitional.Formula.FreeClosed, hw, hn, hr, Fin.forall_fin_succ]

theorem tg_program_packet_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω n r : Term d) :
    Formula.satisfies ρ (tg_program_packet_m ω n r) ↔
      Tg_program_packet_d hZF (ω.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [tg_program_packet_m, Tg_program_packet_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_quad_sat_l hZF.1, rd_triple0_sat_l hZF.1, ts_program_sat_l hZF, tt_eval_cases_l, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_program_packet_exists_l {ω H n : M.Domain} (hω : M.IsOmega ω) (hH : V_d I ω H) (hn : M.mem n ω) :
    ∃ r, M.mem r H ∧ Tg_program_packet_d hZF ω n r := by
  obtain ⟨b, σ, a, z, prog⟩ := ts_program_l hZF hω hn
  have algebra := sc_v_algebra_l hZFC (hω.isLimitOrdinal hZF) hH
  have bound j := ZF.v_ordinal_mem_l I hZF hH (hω.transitive hZF b prog.length (σ j) (prog.slots j))
  obtain ⟨p, hp, cp⟩ := sc_quad_l algebra (bound 0) (bound 1) (bound 2) (bound 3)
  obtain ⟨q', hq', cq'⟩ := algebra.kpair_l (bound 5) (bound 6)
  obtain ⟨q, hq, cq⟩ := algebra.kpair_l (bound 4) hq'
  obtain ⟨r, hr, cr⟩ := sc_quad_l algebra (ZF.v_ordinal_mem_l I hZF hH prog.length)
    (ZF.v_ordinal_mem_l I hZF hH prog.natural) hp hq
  refine ⟨r, hr, b, z, p, q, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6, a, cr, cp, ⟨q', cq', cq⟩, ?_⟩
  have eq : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) j
  rw [eq]
  exact prog

def Tg_program_catalog_d (ω H Γ : M.Domain) : Prop := Fn0_d ω H Γ ∧
  ∀ n r, Rd_entry_d n r Γ → Tg_program_packet_d hZF ω n r

theorem tg_program_catalog_l {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ H Γ, V_d I ω H ∧ Tg_program_catalog_d hZFC ω H Γ ∧ M.MemberSubset Γ H := by
  obtain ⟨H, hH⟩ := ZF.v_exists_l I hZF (hω.isOrdinal hZF)
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : BinarySchema 1 := { body := tg_program_packet_m (.bound 2) (.bound 1) .newest }
  have sat n r : φ.denote ρ n r ↔ Tg_program_packet_d hZF ω n r := tg_program_packet_sat_l hZF ..
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := ω) (Y := H) (fun n hn => by
    obtain ⟨r, hr, packet⟩ := tg_program_packet_exists_l hZFC hω hH hn
    exact ⟨r, hr, (sat n r).mpr packet⟩)
  refine ⟨H, Γ, hH, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, fun n r hr => (sat n r).mp (all n r hr)⟩, ?_⟩
  intro p hp
  obtain ⟨n, r, pair⟩ := fn.1.1 p hp
  have entry : Rd_entry_d n r Γ := ⟨p, pair, hp⟩
  obtain ⟨p', hp', pair'⟩ := (sc_v_algebra_l hZFC (hω.isLimitOrdinal hZF) hH).kpair_l
    (ZF.v_ordinal_mem_l I hZF hH (fn.input_mem_of_pairMember entry)) (fn.output_mem_of_pairMember entry)
  exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

end YesMetaZFC.SetTheory.LargeCardinal

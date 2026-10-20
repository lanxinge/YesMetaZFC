import YesMetaZFC.Model.SetTheory.Internal.ProgramRecodeSource
import YesMetaZFC.Model.SetTheory.Internal.CanonicalLocal

/-! # 从原自然数码恢复平坦程序的有界公式

自然数编号仍采用原 Kuratowski 规范编码。平坦程序只作为解码所得程序的
等义表示；转换证书的所有见证都留在实际的极限秩层中。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_flat_d (I : kpair_convention_l.Interpretation M) (K : FlatPairing.convention.Interpretation M)
    (ω z G n r : M.Domain) : Prop := ∃ a F,
  Sc_num_d I ω a z ∧ Sformula_d I ω a n F r ∧ Sx_program_d I K F G

def sc_flat_m {d} (ω z G n r : Term d) : Formula 1 d := set[d] ⟪∃ a F,
  ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, ⌜z⌝ₛ) ∧
  ⌜sformula_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, a, ⌜n⌝ₛ, F, ⌜r⌝ₛ) ∧
  ⌜sx_program_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(F, ⌜G⌝ₛ)⟫
derive_free_closed sc_flat_m

theorem sc_flat_sat_l (I : kpair_convention_l.Interpretation M) (K : FlatPairing.convention.Interpretation M)
    (hE : Extensional M) {d} (ρ : Env M d) (ω z G n r : Term d) :
    Formula.satisfies ρ (sc_flat_m ω z G n r) ↔
      Sc_flat_d I K (ω.eval ρ) (z.eval ρ) (G.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [sc_flat_m, Sc_flat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sc_num_sat_l I hE, sformula_sat_l I hE, sx_program_sat_l I K hE, Definitional.Term.eval_weaken]; rfl

def sc_flat_local_m {d} (Z ω z G n r : Term d) : Formula 1 d :=
  lr_rel_m (sc_flat_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)) Z
    (Fin.cases r (Fin.cases n (Fin.cases G (Fin.cases z (fun _ => ω)))))

@[simp] theorem sc_flat_local_closed_l {d} (Z ω z G n r : Term d)
    (hZ : Z.freeSupport = []) (hω : ω.freeSupport = []) (hz : z.freeSupport = [])
    (hG : G.freeSupport = []) (hn : n.freeSupport = []) (hr : r.freeSupport = []) :
    (sc_flat_local_m Z ω z G n r).FreeClosed :=
  lr_rel_closed_l _ (sc_flat_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) Z _ hZ
    (Fin.cases hr (Fin.cases hn (Fin.cases hG (Fin.cases hz (fun _ => hω)))))

theorem sc_flat_local_delta_l {d} (Z ω z G n r : Term d) : (sc_flat_local_m Z ω z G n r).IsDelta0 :=
  lr_rel_delta_l ..

variable (hZF : M.Models ZF) {ω δ Z : M.Domain} (hω : M.IsOmega ω)
  (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (hωZ : M.mem ω Z)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => ZF.v_transitive_l I hZF hV
local notation "nz" => Nonempty.intro (Subtype.mk ω hωZ)
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) (sc_v_pair_l hZF hδ hV)
local notation "L" => fp_rank_interpretation_l I hZF hω hV hωZ

theorem rt_sc_flat_l (z G n r : (N).Domain) :
    Sc_flat_d J L ⟨ω, hωZ⟩ z G n r ↔ Sc_flat_d I K ω z.val G.val n.val r.val := by
  have num := rt_sc_num_l hZF hδ hV nz
  have syn := rt_sformula_l (ZF.modelsKP hZF) T nz (sc_v_pair_l hZF hδ hV)
  constructor
  · rintro ⟨a, F, ha, hf, code⟩
    exact ⟨a.val, F.val, (num _ a z hω).mp ha, (syn _ a n F r).mp hf,
      (rt_sx_program_l hZF hω hV hωZ hδ F G).mp code⟩
  · rintro ⟨a, F, ha, hf, code⟩
    obtain ⟨C, hc⟩ := scode_exists_l I hZF hω
    have hC := scode_rank_mem_l hZF hω hδ hV hωZ hc
    have hA := T C hC a ((hc a).mpr ⟨n.val, F, r.val, hf⟩)
    let a' : (N).Domain := ⟨a, hA⟩
    let F' : (N).Domain := ⟨F, (hf.1.mem_l M T hA).1⟩
    exact ⟨a', F', (num _ a' z hω).mpr ha, (syn _ a' n F' r).mpr hf,
      (rt_sx_program_l hZF hω hV hωZ hδ F' G).mpr code⟩

include hω hδ hV hωZ in
theorem sc_flat_local_sat_l {d} (ρ : Env M d) (U w z G n r : Term d)
    (hU : U.eval ρ = Z) (hw : w.eval ρ = ω) (hz : M.mem (z.eval ρ) Z)
    (hG : M.mem (G.eval ρ) Z) (hn : M.mem (n.eval ρ) Z) (hr : M.mem (r.eval ρ) Z) :
    Formula.satisfies ρ (sc_flat_local_m U w z G n r) ↔
      Sc_flat_d I K ω (z.eval ρ) (G.eval ρ) (n.eval ρ) (r.eval ρ) := by
  let η : Env N 5 := ⟨Fin.cases ⟨r.eval ρ, hr⟩ (Fin.cases ⟨n.eval ρ, hn⟩
    (Fin.cases ⟨G.eval ρ, hG⟩ (Fin.cases ⟨z.eval ρ, hz⟩ (fun _ => ⟨ω, hωZ⟩)))), fun _ => ⟨ω, hωZ⟩⟩
  let φ := sc_flat_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)
  exact (sc_relative_sat_l T nz φ (sc_flat_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl)
    η ρ U _ hU (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))))).trans
    ((sc_flat_sat_l J L (rt_model_ext_l hZF.1 T nz) η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
      (rt_sc_flat_l hZF hω hδ hV hωZ ..))

end YesMetaZFC.SetTheory.Internal

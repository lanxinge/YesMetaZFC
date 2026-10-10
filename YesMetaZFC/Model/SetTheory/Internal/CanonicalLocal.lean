import YesMetaZFC.Model.SetTheory.Internal.CanonicalSource
import YesMetaZFC.Model.SetTheory.Internal.RankSkolem
import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax

/-! # 在实际极限秩层内运行原规范解码器

将解码器的全部量词限制到指定秩层，得到一条有界公式。
程序码和自然数码的秩界由已有代码全集自动供应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_num_local_m {d} (Z ω a z : Term d) : Formula 1 d := .conj (.mem a Z) (.conj (.mem z Z)
  (lr_rel_m (sc_num_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) (.newest : Term 3)) Z
    (Fin.cases z (Fin.cases a (fun _ => ω)))))

@[simp] theorem sc_num_local_closed_l {d} (Z ω a z : Term d)
    (hZ : Z.freeSupport = []) (hω : ω.freeSupport = []) (ha : a.freeSupport = []) (hz : z.freeSupport = []) :
    (sc_num_local_m Z ω a z).FreeClosed := by
  simp only [sc_num_local_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨ha, hZ⟩, ⟨⟨hz, hZ⟩, lr_rel_closed_l _ (sc_num_m_freeClosed _ _ _ rfl rfl rfl) Z _ hZ
    (Fin.cases hz (Fin.cases ha (fun _ => hω)))⟩⟩

theorem sc_num_local_delta_l {d} (Z ω a z : Term d) : (sc_num_local_m Z ω a z).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (lr_rel_delta_l ..))

/-- 对任意候选码均成立，包括无效码；没有额外解码表或源理论前提。 -/
theorem sc_num_local_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (Z ω a z : Term d)
    {δ} (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ (Z.eval ρ))
    (hω : M.IsOmega (ω.eval ρ)) (hωZ : M.mem (ω.eval ρ) (Z.eval ρ)) :
    Formula.satisfies ρ (sc_num_local_m Z ω a z) ↔
      Sc_num_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (a.eval ρ) (z.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := ZF.v_transitive_l I hZF hV
  let nz : Nonempty {x // M.mem x (Z.eval ρ)} := ⟨⟨ω.eval ρ, hωZ⟩⟩
  let N := rt_model_l (Z.eval ρ) nz
  let J := rt_pair_l trans nz hZF.1 (sc_v_pair_l hZF hδ hV)
  let φ := sc_num_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1) (.newest : Term 3)
  have read (ha : M.mem (a.eval ρ) (Z.eval ρ)) (hz : M.mem (z.eval ρ) (Z.eval ρ)) :
      Formula.satisfies ρ (lr_rel_m φ Z (Fin.cases z (Fin.cases a (fun _ => ω)))) ↔
        Sc_num_d I (ω.eval ρ) (a.eval ρ) (z.eval ρ) := by
    let w : N.Domain := ⟨ω.eval ρ, hωZ⟩
    let b : N.Domain := ⟨a.eval ρ, ha⟩
    let v : N.Domain := ⟨z.eval ρ, hz⟩
    let η : Env N 3 := ⟨Fin.cases v (Fin.cases b (fun _ => w)), fun _ => w⟩
    obtain ⟨c, R, hc, hR⟩ := smdl_membership_l I hZF ⟨ω.eval ρ, hωZ⟩
    exact (sc_relative_sat_l I ⟨hc, hR⟩ trans nz φ (sc_num_m_freeClosed _ _ _ rfl rfl rfl)
      η ρ Z _ rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).trans
        ((sc_num_sat_l J (rt_model_ext_l hZF.1 trans nz) η (.bound 2) (.bound 1) .newest).trans
          (rt_sc_num_l hZF hδ hV nz w b v hω))
  simp only [sc_num_local_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  constructor
  · exact fun ⟨ha, hz, h⟩ => (read ha hz).mp h
  · intro h
    obtain ⟨C, code⟩ := scode_exists_l I hZF hω
    have data := h
    obtain ⟨n, F, k, _, _, hf, _⟩ := data
    have ha := trans C (scode_rank_mem_l hZF hω hδ hV hωZ code) (a.eval ρ)
      ((code (a.eval ρ)).mpr ⟨n, F, k, hf⟩)
    have hz := trans (ω.eval ρ) hωZ (z.eval ρ) (sc_num_natural_l I hZF hω h)
    exact ⟨ha, hz, (read ha hz).mpr h⟩

end YesMetaZFC.SetTheory.Internal

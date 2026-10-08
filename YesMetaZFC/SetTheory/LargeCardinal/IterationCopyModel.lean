import YesMetaZFC.SetTheory.LargeCardinal.IterationModel
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderOmegaClosed

/-! # 整树复制中的可数闭工作模型

状态只保留后继实际使用的闭性、秩层、幂集、小覆盖及不可达闭包。
正规秩层给出初值；同一实际超幂保持全部字段。原公式可直接交给类依赖选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ic_model_d (hZF : M.Models ZF) (ω κ K X R : M.Domain) : Prop where
  source : Ep_source_d hZF ω κ K X R
  closed : Sc_omega_closed_d ω X
  hierarchy : Sc_hierarchy_d X
  power : Sc_power_d X
  cover : Sc_cover_d X
  inaccessible : Sc_inaccessible_closure_d (kp_pair_l (ZF.modelsKP hZF)) ω X

def ic_closure_m {d} (ω X : Term d) : Formula 1 d :=
  lr_rel_m (n := 1) (sc_inaccessible_closure_m .newest) X (fun _ => ω)
derive_free_closed ic_closure_m

def ic_model_m {d} (ω κ K X R : Term d) : Formula 1 d := .conj (ep_source_m ω κ K X R)
  (.conj (sc_omega_closed_m ω X) (.conj (pn_structure_m X) (ic_closure_m ω X)))
derive_free_closed ic_model_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_model_sat_l {d} (ρ : Env M d) (ω κ K X R : Term d) :
    Formula.satisfies ρ (ic_model_m ω κ K X R) ↔
      Ic_model_d hZF (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) := by
  have read (s : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ)) :
      (Formula.satisfies ρ (pn_structure_m X) ∧ Formula.satisfies ρ (ic_closure_m ω X)) ↔
        (Sc_hierarchy_d (X.eval ρ) ∧ Sc_power_d (X.eval ρ) ∧ Sc_cover_d (X.eval ρ)) ∧
          Sc_inaccessible_closure_d I (ω.eval ρ) (X.eval ρ) := by
    obtain ⟨c, hm⟩ := s.code
    let nx : Nonempty {x // M.mem x (X.eval ρ)} := ⟨⟨ω.eval ρ, s.omega_mem⟩⟩
    let η : Env (rt_model_l (X.eval ρ) nx) 0 := ⟨Fin.elim0, fun _ => ⟨ω.eval ρ, s.omega_mem⟩⟩
    let θ : Env (rt_model_l (X.eval ρ) nx) 1 := ⟨fun _ => ⟨ω.eval ρ, s.omega_mem⟩, η.free⟩
    have base := sc_relative_sat_l I hm s.transitive nx
      (.conj sc_hierarchy_m (.conj sc_power_m sc_cover_m)) (by simp -implicitDefEqProofs [sc_hierarchy_m, Definitional.Formula.FreeClosed])
      η ρ X Fin.elim0 rfl (fun i => Fin.elim0 i)
    have closure := sc_relative_sat_l I hm s.transitive nx (sc_inaccessible_closure_m .newest)
      (by simp -implicitDefEqProofs) θ ρ X (fun _ => ω) rfl (fun _ => rfl)
    simp only [Formula.satisfies_conj_iff, sc_hierarchy_sat_l (ZF.modelsKP hZF) s.transitive nx,
      sc_power_sat_l s.transitive nx, sc_cover_sat_l s.transitive nx] at base
    rw [sc_inaccessible_closure_sat_l (ZF.modelsKP hZF) s.transitive s.theory.algebra.pair nx θ .newest] at closure
    exact and_congr base closure
  simp only [ic_model_m, Formula.satisfies_conj_iff, ep_source_sat_l hZF, sc_omega_closed_sat_l hZF.1]
  exact ⟨fun ⟨s, c, h⟩ => let ⟨⟨v, p, b⟩, i⟩ := (read s).mp h; ⟨s, c, v, p, b, i⟩,
    fun h => ⟨h.source, h.closed, (read h.source).mpr ⟨⟨h.hierarchy, h.power, h.cover⟩, h.inaccessible⟩⟩⟩

theorem Ic_model_d.rebase_l {ω κ K X R μ : M.Domain} (h : Ic_model_d hZF ω κ K X R)
    (hμ : M.mem μ X) (above : M.MemberSubset ω μ) (small : Sc_small_d X μ) :
    ∃ K', Ic_model_d hZF ω μ K' X R := by
  obtain ⟨K', s⟩ := h.source.rebase_l hZF hμ above small
  exact ⟨K', s, h.closed, h.hierarchy, h.power, h.cover, h.inaccessible⟩

variable (hZFC : M.Models ZFC)

theorem ic_regular_model_l {ω δ V : M.Domain} (hω : M.IsOmega ω) (above : M.mem ω δ)
    (regular : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) :
    ∃ K R, Ic_model_d (ZFC.models_zf_l hZFC) ω ω K V R := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K, seq⟩ := ZF.fseq_space_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω ω
  obtain ⟨R, s⟩ := ep_regular_source_l hZFC hω above regular rank above (fun _ h => h) seq
  exact ⟨K, R, s, sc_v_omega_closed_l hZF regular above rank s.omega_mem,
    sc_v_hierarchy_l hZF regular.isLimitOrdinal rank, sc_v_power_l hZF regular.isLimitOrdinal rank,
    sc_v_cover_l hZF rank, sc_v_inaccessible_closure_l hZFC hω regular.isLimitOrdinal rank⟩

/-- 所属源只须对有界值域可数闭；工作源的完整闭性由同一个超幂保持。 -/
theorem Ic_model_d.ultra_l {ω κ K X R K' Y R' L F c d N S j : M.Domain}
    (h : Ic_model_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (owner : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R') (agree : Ea_agree_d ω κ X Y)
    (closed : Sc_bounded_omega_closed_d ω Y) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) Y L)
    (hL : M.IsLimitOrdinal L) (loc : It_local_d ω Y κ L F) (strength : Ex_strength_d (ZFC.models_zf_l hZFC) ω κ L Y F)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (ultra : It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F c d j) :
    ∃ K₀, Ic_model_d (ZFC.models_zf_l hZFC) ω ω K₀ N S := by
  let hZF := ZFC.models_zf_l hZFC
  have hN := ultra.transitive_l hZF hn.1
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hw := hj.omega_l (kp_pair_l (ZF.modelsKP hZF)) hZF h.source.omega h.source.transitive hN hm hn h.source.omega_mem
  obtain ⟨K₀, s⟩ := h.source.successor_l hZF hm hn hN hj (hj.1.1.output_mem_of_pairMember hw) (fun _ h => h)
    ((hj.small_l hZF h.source.omega h.source.transitive hN hm hn hw).mp (h.source.cardinal_small.mono_l h.source.below))
  exact ⟨K₀, s, ultra.closed_l hZFC h.source owner agree h.closed closed h.hierarchy h.power op oc bound sizes hL loc strength hm hn,
    (sc_hierarchy_iff_l hZF h.source.omega h.source.transitive hN hm hn hj).mp h.hierarchy,
    (sc_power_iff_l hZF h.source.omega h.source.transitive hN hm hn hj).mp h.power,
    (sc_cover_iff_l hZF h.source.omega h.source.transitive hN hm hn hj).mp h.cover,
    (sc_inaccessible_closure_iff_l hZF h.source.omega h.source.transitive hN h.source.theory.algebra.pair
      s.theory.algebra.pair hm hn hj h.source.omega_mem).mp h.inaccessible⟩

end YesMetaZFC.SetTheory.LargeCardinal

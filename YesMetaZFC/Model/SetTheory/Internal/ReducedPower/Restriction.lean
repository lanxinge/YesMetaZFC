import YesMetaZFC.Model.SetTheory.Internal.SourceField
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullProjection
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceProjection
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 限制测度保持同一个源超幂

代表的精确原子真值集属于源。完整测度与其源内限制因此给出相同的代表
等价及关系，同一个类集合、投影和结构码直接取得限制测度证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}}

theorem sc_member_trace_l (hZF : M.Models ZF) {ω c X R D f g : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hD : M.mem D X) (hf : Sfun_d X D f) (hg : Sfun_d X D g) : ∃ A, M.mem A X ∧
      ∀ v, M.mem v A ↔ M.mem v D ∧ Rp_atom_d (kp_pair_l (ZF.modelsKP hZF)) false X R f g v := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hfX, B, hBX, hFB⟩ := hf
  obtain ⟨hgX, C, hCX, hGC⟩ := hg
  let ρ := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push C).push f).push g
  let φ : UnarySchema 4 := { body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 4))
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 3)) (.mem (.bound 1) .newest)))) }
  obtain ⟨A, hAX, spec⟩ := sc_separate_source_l I hZF hω hX hm theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.mem _ _)))))
    ρ (Fin.cases hgX (Fin.cases hfX (Fin.cases hCX (fun _ => hBX)))) hD
  refine ⟨A, hAX, fun v => (spec v).trans (and_congr_right fun _ => ?_)⟩
  have read : φ.denote ρ v ↔ ∃ x, M.mem x B ∧ ∃ y, M.mem y C ∧ Rd_entry_d v x f ∧ Rd_entry_d v y g ∧ M.mem x y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  refine read.trans ⟨?_, ?_⟩
  · rintro ⟨x, hx, y, hy, hfx, hgy, hxy⟩
    exact ⟨x, hX B hBX x hx, y, hX C hCX y hy, hfx, hgy,
      (hm.2 x y).mpr ⟨hX B hBX x hx, hX C hCX y hy, hxy⟩⟩
  · rintro ⟨x, _, y, _, hfx, hgy, hxy⟩
    exact ⟨x, (hFB.bound_l hfx).2, y, (hGC.bound_l hgy).2, hfx, hgy, ((hm.2 x y).mp hxy).2.2⟩

theorem rp_change_filter_l (I : kpair_convention_l.Interpretation M) {D X U V R c G p C T : M.Domain}
    (h : Rp_model_d I D X U R c G p C T)
    (eq : ∀ f g, M.mem f G → M.mem g G → (Rp_eq_d X U f g ↔ Rp_eq_d X V f g))
    (rel : ∀ f g, M.mem f G → M.mem g G → (Rp_rel_d I X U R f g ↔ Rp_rel_d I X V R f g)) :
    Rp_model_d I D X V R c G p C T := by
  refine ⟨⟨h.map.functions, h.map.projection, h.map.range, fun f B => ?_⟩, h.code, fun f g B E hf hg =>
    (h.relation f g B E hf hg).trans (rel f g (h.map.projection.input_mem_of_pairMember hf) (h.map.projection.input_mem_of_pairMember hg))⟩
  refine (h.map.classes f B).trans (and_congr_right fun hf => forall_congr' fun g => iff_congr Iff.rfl ?_)
  exact and_congr_right fun hg => eq f g hf hg

theorem rs_restrict_model_l (hZF : M.Models ZF) {ω c X R D U o G p C T : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hD : M.mem D X) (hU : Sf_ultra_d X D U)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f)
    (model : Rp_model_d (kp_pair_l (ZF.modelsKP hZF)) D X U R o G p C T) :
    ∃ P V, Source_d X D P ∧ Rel_ultra_d D P V ∧ (∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U) ∧
      Rp_model_d (kp_pair_l (ZF.modelsKP hZF)) D X V R o G p C T := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P, V, hP, hV, hv⟩ := sc_source_ultrafilter_l I hZF hω hX hm theory hD hU
  have sf f (hf : M.mem f G) := sc_function_domain_l hZF hω hX hm theory hD ((hG f).mp hf).1 ((hG f).mp hf).2
  have transfer (ψ : M.Domain → Prop) A (hAX : M.mem A X) (ha : ∀ v, M.mem v A ↔ M.mem v D ∧ ψ v) :
      (∃ B, M.mem B U ∧ ∀ v, M.mem v B → ψ v) ↔ ∃ B, M.mem B V ∧ ∀ v, M.mem v B → ψ v := by
    refine ⟨fun ⟨B, hb, ht⟩ => ?_, fun ⟨B, hb, ht⟩ => ⟨B, ((hv B).mp hb).2, ht⟩⟩
    have haU := hU.upward B A hb hAX (fun v hv => ((ha v).mp hv).1)
      (fun v hv => (ha v).mpr ⟨hU.base.bounds B hb v hv, ht v hv⟩)
    exact ⟨A, (hv A).mpr ⟨(hP A).mpr ⟨hAX, fun v hv => ((ha v).mp hv).1⟩, haU⟩, fun v hv => ((ha v).mp hv).2⟩
  refine ⟨P, V, hP, hV, hv, rp_change_filter_l I model ?_ ?_⟩
  · intro f g hf hg
    obtain ⟨A, hAX, ha⟩ := sc_equalizer_l I hZF hω hX hm theory hD (sf f hf) ((hG g).mp hg).1
    exact transfer _ A hAX ha
  · intro f g hf hg
    obtain ⟨A, hAX, ha⟩ := sc_member_trace_l hZF hω hX hm theory hD (sf f hf) (sf g hg)
    exact transfer _ A hAX ha

end YesMetaZFC.SetTheory.Internal

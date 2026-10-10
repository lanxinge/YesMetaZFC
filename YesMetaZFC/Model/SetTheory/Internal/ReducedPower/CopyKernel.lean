import YesMetaZFC.Model.SetTheory.Internal.SourceTransport
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceProjection
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Lift

/-! # 不同源超幂之间的代表复制与等价核

实际初等图 π 将 f 送到 π(f)。只要求两个测度在源中子集及其 π 像上
精确对应；不要求 π 的像穷尽新定义域，也不要求任一测度测量背景全部子集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_copy_family_l {ω c d X R Y S π D D' G H : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (theory : Sc_theory_d I ω X R) (hD : M.PairMember I D D' π)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f)
    (hH : ∀ f, M.mem f H ↔ M.mem f Y ∧ Fn0_d D' Y f) :
    ∃ K, M.IsSetFunctionFromTo I K G H ∧ ∀ f g, M.PairMember I f g K ↔ M.mem f G ∧ M.PairMember I f g π := by
  obtain ⟨K, hk⟩ := ZF.exists_restriction hZF I π G
  have hf := hk.isSetFunctionFromTo hπ.1.1 (fun f hf => ((hG f).mp hf).1)
  have bound f g (hfg : M.PairMember I f g K) : M.mem g H := by
    obtain ⟨hf, hfg⟩ := (hk.2 f g).mp hfg
    have sf := sc_function_domain_l theory.algebra
      ((hG f).mp hf).1 ((hG f).mp hf).2
    have sg := hπ.sfun_l hZF hω hX hY hm hn hD hfg sf
    exact (hH g).mpr ⟨sg.1, sg.function_l hY⟩
  exact ⟨K, ⟨hf.1, hf.2.1, fun f hfG => (hf.2.2 f hfG).imp fun g hg => ⟨bound f g hg.2, hg.2⟩⟩, hk.2⟩

theorem rs_copy_equalizer_l {ω c d X R Y S π D D' f f' g g' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (theory : Sc_theory_d I ω X R) (hD : M.PairMember I D D' π)
    (hff : M.PairMember I f f' π) (hgg : M.PairMember I g g' π)
    (hf : Sfun_d X D f) (hg : Sfun_d X D g) : ∃ A A', M.mem A X ∧ M.PairMember I A A' π ∧
      (∀ v, M.mem v A ↔ M.mem v D ∧ ∃ x, M.mem x X ∧ Rd_entry_d v x f ∧ Rd_entry_d v x g) ∧
      (∀ v, M.mem v A' ↔ M.mem v D' ∧ ∃ x, M.mem x Y ∧ Rd_entry_d v x f' ∧ Rd_entry_d v x g') := by
  obtain ⟨A, hAX, spec⟩ := sc_equalizer_l I hZF hω hX hm theory (hπ.1.1.input_mem_of_pairMember hD) hf hg.1
  obtain ⟨_, B, hBX, hfb⟩ := hf
  obtain ⟨B', hBY, hBB⟩ := hπ.1.1.2.2 B hBX
  obtain ⟨A', _, hAA⟩ := hπ.1.1.2.2 A hAX
  let φ : Formula 1 5 := .conj (Formula.subset (.bound 3) (.bound 4))
    (Formula.forallMem (.bound 4) (.iff (.mem .newest (.bound 4))
      (Formula.existsMem (.bound 3) (.conj (rd_entry0_m (.bound 1) .newest (.bound 3))
        (rd_entry0_m (.bound 1) .newest (.bound 2))))))
  have tr := smap_delta_l I hZF hω hX hY hm hn hπ φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
    ⟨Fin.cases g (Fin.cases f (Fin.cases B (Fin.cases A (fun _ => D)))), fun _ => D⟩
    ⟨Fin.cases g' (Fin.cases f' (Fin.cases B' (Fin.cases A' (fun _ => D')))), fun _ => D'⟩
    (Fin.cases hgg (Fin.cases hff (Fin.cases hBB (Fin.cases hAA (fun _ => hD)))))
  simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] at tr
  have target := tr.mp ⟨fun v hv => ((spec v).mp hv).1, fun v hv => (spec v).trans
    ⟨fun ⟨_, x, _, hx, hg⟩ => ⟨x, (hfb.bound_l hx).2, hx, hg⟩,
      fun ⟨x, hx, hf, hg⟩ => ⟨hv, x, hX B hBX x hx, hf, hg⟩⟩⟩
  have fb' : Fn0_d D' B' f' := by
    have tr := smap_delta_l I hZF hω hX hY hm hn hπ (n := 3) (fn0_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (fn0_delta_l ..)
      ⟨Fin.cases f (Fin.cases B (fun _ => D)), fun _ => D⟩
      ⟨Fin.cases f' (Fin.cases B' (fun _ => D')), fun _ => D'⟩ (Fin.cases hff (Fin.cases hBB (fun _ => hD)))
    exact (fn0_sat_l hZF.1 ..).mp (tr.mp ((fn0_sat_l hZF.1 ..).mpr hfb))
  refine ⟨A, A', hAX, hAA, spec, fun v => ⟨?_, ?_⟩⟩
  · intro hv
    have hd := target.1 v hv
    obtain ⟨x, hx, hf, hg⟩ := (target.2 v hd).mp hv
    exact ⟨hd, x, hY B' hBY x hx, hf, hg⟩
  · rintro ⟨hv, x, _, hf, hg⟩
    exact (target.2 v hv).mpr ⟨x, (fb'.bound_l hf).2, hf, hg⟩

theorem rs_copy_kernel_l {ω c d X R Y S π D D' P Q U V f f' g g' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (theory : Sc_theory_d I ω X R) (hD : M.PairMember I D D' π)
    (hP : Source_d X D P) (hQ : Source_d Y D' Q) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d D' Q V)
    (measure : ∀ A A', M.mem A P → M.PairMember I A A' π → (M.mem A U ↔ M.mem A' V))
    (hff : M.PairMember I f f' π) (hgg : M.PairMember I g g' π)
    (hf : Sfun_d X D f) (hg : Sfun_d X D g) : Rp_eq_d X U f g ↔ Rp_eq_d Y V f' g' := by
  obtain ⟨A, A', hAX, hAA, old, next⟩ := rs_copy_equalizer_l hZF hω hX hY hm hn hπ theory hD hff hgg hf hg
  have haP := (hP A).mpr ⟨hAX, fun v hv => ((old v).mp hv).1⟩
  have haQ := (hQ A').mpr ⟨hπ.1.1.output_mem_of_pairMember hAA, fun v hv => ((next v).mp hv).1⟩
  have read {D P U Z f g A : M.Domain} (hU : Rel_ultra_d D P U) (hA : M.mem A P)
      (spec : ∀ v, M.mem v A ↔ M.mem v D ∧ ∃ x, M.mem x Z ∧ Rd_entry_d v x f ∧ Rd_entry_d v x g) :
      M.mem A U ↔ Rp_eq_d Z U f g :=
    ⟨fun h => ⟨A, h, fun v hv => ((spec v).mp hv).2⟩, fun ⟨B, hb, ht⟩ =>
      hU.upward B A hb hA (fun v hv => (spec v).mpr ⟨hU.base.bounds B hb v hv, ht v hv⟩)⟩
  exact (read hU haP old).symm.trans ((measure A A' haP hAA).trans (read hV haQ next))

end YesMetaZFC.SetTheory.Internal

import YesMetaZFC.Model.SetTheory.Internal.PointwiseTrace
import YesMetaZFC.Model.SetTheory.Internal.SeparationTransport
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega

/-! # 不同源之间的代表函数与真值集合搬运

函数图由有界初等性搬运；逐点公式用同一编译程序，指定分离集用完整
初等性搬运。因此像集合包含新定义域上的全部正确点，而非只有旧点的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.sfun_l {ω c d X R Y S q D D' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hD : M.PairMember I D D' q) (hF : M.PairMember I f f' q) (hf : Sfun_d X D f) : Sfun_d Y D' f' := by
  obtain ⟨_, C, hC, hc⟩ := hf
  obtain ⟨C', hC', hCC⟩ := hq.1.1.2.2 C hC
  have transfer := smap_delta_l I hZF hω hX hY hm hn hq (n := 3)
    (fn0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fn0_delta_l ..)
    ⟨Fin.cases f (Fin.cases C (fun _ => D)), fun _ => D⟩
    ⟨Fin.cases f' (Fin.cases C' (fun _ => D')), fun _ => D'⟩ (Fin.cases hF (Fin.cases hCC (fun _ => hD)))
  simp only [fn0_sat_l hZF.1] at transfer
  exact ⟨hq.1.1.output_mem_of_pairMember hF, C', hC', transfer.mp hc⟩

theorem Smap_d.pe_trace_l {ω c d X R Y S q D D' E K F n r b a a' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (source : Sc_theory_d I ω X R) (target : Sc_theory_d I ω Y S)
    (hD : M.PairMember I D D' q) (hE : M.IsFunctionSpace I E ω X) (hK : M.IsFunctionSpace I K ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (ha' : M.mem a' K) (repr : Pe_repr_d I b D X R a)
    (repr' : Pe_repr_d I b D' Y S a') (assign : Smap_assign_d I ω q a a') :
    ∃ A A', M.mem A X ∧ M.PairMember I A A' q ∧
      (∀ v, M.mem v A ↔ M.mem v D ∧ Pe_sat_d I b D X R E F n r a v) ∧
      (∀ v, M.mem v A' ↔ M.mem v D' ∧ Pe_sat_d I b D' Y S K F n r a' v) := by
  have hDX := hq.1.1.input_mem_of_pairMember hD
  have hDY := hq.1.1.output_mem_of_pairMember hD
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, build⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨k, hk, hrk⟩ := build.2.1.2.2 r hr
  obtain ⟨aD, update, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hDX
  obtain ⟨aD', update', haD'⟩ := senv_update_exists_l I hZF ((hK a').mp ha') hb hDY
  obtain ⟨A, hAX, sep⟩ := source.separation E G m k t aD D hE build.1 hk htω ((hE aD).mpr haD) hDX
  obtain ⟨A', _, hAA⟩ := hq.1.1.2.2 A hAX
  have next := hq.separation_l I hZF hω hX hY hm hn hE hK build.1 hk htω
    ((hE aD).mpr haD) ((hK aD').mpr haD') (assign.update_l I hq.1.1.1 hD update update') hD hAA sep
  exact ⟨A, A', hAX, hAA,
    (pe_separation_mem_l hZF hω hX hm (sc_pe_context_l hZF hω hX hm source hDX hE) hAX hb ht build hrk ha repr update).mp sep,
    (pe_separation_mem_l hZF hω hY hn (sc_pe_context_l hZF hω hY hn target hDY hK) (hq.1.1.output_mem_of_pairMember hAA) hb ht build hrk ha' repr' update').mp next⟩

end YesMetaZFC.SetTheory.Internal

import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness
import YesMetaZFC.Model.SetTheory.Internal.SeparationTransport
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

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
  apply (rf_fun_mem_l I hZF.1 hY hn (hq.1.1.output_mem_of_pairMember hD)).mp
  exact ((rf_fun_mem_l I hZF.1 hX hm (hq.1.1.input_mem_of_pairMember hD)).mpr hf).map_l
    I hZF hω hm.1 hn.1 hq hD hF

/-- 两个原关系源中的同一真值集及其实际像，覆盖全部内部程序和像外新点。 -/
theorem Smap_d.pe_trace_l {ω c d X R Y S q D D' E K F n r b a a' : M.Domain}
    (hω : M.IsOmega ω) (hm : Pe_context_d I ω c X R D E) (hn : Pe_context_d I ω d Y S D' K)
    (hq : Smap_d I ω c d X Y q) (source : Sc_theory_d I ω X R)
    (hD : M.PairMember I D D' q)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (ha' : M.mem a' K) (repr : Pe_repr_d I b D X R a)
    (repr' : Pe_repr_d I b D' Y S a') (assign : Smap_assign_d I ω q a a') :
    ∃ A A', M.mem A X ∧ M.PairMember I A A' q ∧
      (∀ v, M.mem v X → (M.PairMember I v A R ↔ M.PairMember I v D R ∧ Pe_sat_d I b D X R E F n r a v)) ∧
      (∀ v, M.mem v Y → (M.PairMember I v A' S ↔ M.PairMember I v D' S ∧ Pe_sat_d I b D' Y S K F n r a' v)) := by
  have hE := hm.2.2.1
  have hK := hn.2.2.1
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, build⟩ := pe_compile_bound_l hZF hω hF hb hB ht
  obtain ⟨k, hk, hrk⟩ := build.2.1.2.2 r hr
  obtain ⟨aD, update, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hm.2.2.2.1
  obtain ⟨aD', update', haD'⟩ := senv_update_exists_l I hZF ((hK a').mp ha') hb hn.2.2.2.1
  obtain ⟨A, hAX, sep⟩ := source.separation E G m k t aD D hE build.1 hk htω ((hE aD).mpr haD) hm.2.2.2.1
  obtain ⟨A', _, hAA⟩ := hq.1.1.2.2 A hAX
  have next := hq.separation_l I hZF hω hm.2.1 hn.2.1 hE hK build.1 hk htω
    ((hE aD).mpr haD) ((hK aD').mpr haD') (assign.update_l I hq.1.1.1 hD update update') hD hAA sep
  exact ⟨A, A', hAX, hAA,
    (pe_separation_l hZF hω hm hb ht build hrk ha repr update).mp sep,
    (pe_separation_l hZF hω hn hb ht build hrk ha' repr' update').mp next⟩

end YesMetaZFC.SetTheory.Internal

import YesMetaZFC.Model.SetTheory.Internal.SubtypeEmbedding
import YesMetaZFC.Model.SetTheory.Internal.TypeEmbedding

/-! # 从前驱类型的像返回原类型的像

高处的实现只用于证明源类型的有界闭包性质。实际嵌入仅作用于低秩源；
目标中的新查询经同一闭包性质读取，不要求嵌入扩张到实现所在的高秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.subtype_minus_l {ω θ X R c Z S d j n b a z U D u w D' u' w' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hZ : M.TransitiveSet Z) (hm : Smem_d I c X R) (hn : Smem_d I d Z S)
    (hj : Smap_d I ω c d X Z j) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hUX : M.mem U X) (hD : Rd_entry_d D D' j) (hu : Rd_entry_d u u' j) (hw : Rd_entry_d w w' j)
    (minus : Tm_minus_d I ω D u w)
    {ν μ A Y c₀ R₀ d₀ S₀ s δ : M.Domain} (hA : V_d I ν A) (hY : V_d I μ Y) (hs : M.SuccessorOf μ ν)
    (lower : Smem_d I c₀ A R₀) (upper : Smem_d I d₀ Y S₀) (type : Tt_realized_d I ω d₀ Y S₀ n s δ U D u)
    (tuple : Fn0_d n A s) (point : M.mem δ A) (constants : M.MemberSubset U A)
    {q C H : M.Domain} (pair : (I).Codes q z C) (column : Fn0_d b H C)
    (omega : ∃ e, KPair_d M e ω ω ∧ Rd_entry_d (σ 6) e C) : M.mem q w' → M.mem q u' := by
  have trans := ZF.v_transitive_l I hZF hX
  have fixed := hj.natural_l hZF hω trans hZ hm hn hωX
  obtain ⟨U', _, hU⟩ := hj.1.1.2.2 U hUX
  obtain ⟨N, E, N', E', names, _, _, hN, hE, _, sequences, product⟩ :=
    hj.type_frame_l hZF hω hX hθ hωX hZ hm hn prog.finite (fixed n prog.finite) hUX hU hD type.pool
  have closed := prog.closure_l hZF hω hA hY hs lower upper type tuple point constants names (E := E)
  have image := (hj.subtype_up_l hZF hω hX hθ hωX hZ hm hn prog.length
    (hω.transitive hZF b prog.length (σ 6) (prog.slots 6)) (sc_num_natural_l I hZF hω prog.code)
    hN hE hD hu).mp closed
  have pred := (hj.type_minus_l hZF hω hX hθ hωX hZ hm hn hD hu hw).mp minus
  have sub := (hj.subset_l hZF hω trans hZ hm hn hu hD).mp (fun p hp => ((type.truth p).mp hp).1)
  intro hq
  obtain ⟨hqD, r, code, hr⟩ := (pred q).mp hq
  have hqZ := hZ D' (hj.1.1.output_mem_of_pairMember hD) q hqD
  have hCZ := (pair.mem_l M hZ hqZ).2
  obtain ⟨z₀, _, C₀, hCE, pair₀⟩ := (product q hqZ).mp hqD
  obtain ⟨ez, eC⟩ := (I).injective pair₀ pair
  subst z₀ C₀
  obtain ⟨b₀, _, col⟩ := (sequences C hCZ).mp hCE
  have eqb := col.domain_eq_l hZF.1 column
  subst b₀
  obtain ⟨e, codeω, edgeω⟩ := omega
  exact image C hCE col ⟨e, (col.bound_l edgeω).2, codeω, edgeω⟩ q hqD r (sub r hr) pair code hr

end YesMetaZFC.SetTheory.Internal

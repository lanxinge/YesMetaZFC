import YesMetaZFC.Model.SetTheory.Internal.SubtypeClause

/-! # 子类型的完整实现见证

较低层中的全赋值提供有限额外变量，实际排列给出 w 的实现顺序。
平坦前缀码相等精确等价于原 n 个变量逐项一致，因此不损失任何原变量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_at_d (hZF : M.Models ZF) (ω δ n s m U D w ν : M.Domain) : Prop :=
  let Q := kp_pair_l (ZF.modelsKP hZF)
  let K := fp_interpretation_l (ZF.models_kpi_l hZF)
  ∃ A c R r g h π, V_d Q ν A ∧ Smem_d Q c A R ∧
    Tt_realized_d Q ω c A R m r δ U D w ∧ M.IsSetFunctionFromTo K g ω A ∧
    M.IsSetFunctionFromTo K h m A ∧ Sx_graph_d Q K r h ∧
    (∀ i x, M.mem i n → (Rd_entry_d i x s ↔ M.PairMember K i x g)) ∧
    M.IsSetBijectionFromTo Q π m m ∧ Tp_perm_d K m A π g h

def Ts_real_d (hZF : M.Models ZF) (ω δ n s m U D w η : M.Domain) : Prop :=
  ∃ ν, M.mem ν η ∧ Ts_at_d hZF ω δ n s m U D w ν

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ts_prefix_l {ω η Y δ n s m U D w g : M.Domain} (hω : M.IsOmega ω) (hY : V_d Q η Y)
    (hn : M.mem n ω) (hwU : M.mem ω U) (fg : M.IsSetFunctionFromTo K g ω Y)
    (same : ∀ i x, M.mem i n → (Rd_entry_d i x s ↔ M.PairMember K i x g)) :
    (∃ p, M.mem p Y ∧ Fs_code_d K ω Y g n p ∧ Ts_below_d hZF ω δ m U D w n p η) ↔
      Ts_real_d hZF ω δ n s m U D w η := by
  constructor
  · rintro ⟨p, _, code, ν, A, c, R, r, f, h, π, hν, hA, model, type, ff, fh, graph, cp, bij, perm⟩
    have sub := ZF.v_mono_l Q hZF hA hY ((v_ordinal_l Q hY).transitive ν hν)
    have ff' : M.IsSetFunctionFromTo K f ω Y := ⟨ff.1, ff.2.1, fun i hi =>
      (ff.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
    have equal := (code.prefix_l K hZF hω fg ff' (cp.mono_l K sub)).mp rfl
    exact ⟨ν, hν, A, c, R, r, f, h, π, hA, model, type, ff, fh, graph,
      fun i x hi => (same i x hi).trans (equal i x hi), bij, perm⟩
  · rintro ⟨ν, hν, A, c, R, r, f, h, π, hA, model, type, ff, fh, graph, orig, bij, perm⟩
    have sub := ZF.v_mono_l Q hZF hA hY ((v_ordinal_l Q hY).transitive ν hν)
    have hwA := type.constants ω hwU
    have hων := (v_ordinal_l Q hA).transitive ω (ZF.v_ordinal_height_l hZF hA (hω.isOrdinal hZF) hwA)
    obtain ⟨p, hp, cp⟩ := fp_finite_rank_l Q hZF hω hA hων ff hn
    have ff' : M.IsSetFunctionFromTo K f ω Y := ⟨ff.1, ff.2.1, fun i hi =>
      (ff.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
    have hωη := (v_ordinal_l Q hY).transitive ω (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal hZF) (sub ω hwA))
    obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hY hωη fg
    exact ⟨p, sub p hp, (cp.mono_l K sub).transport_l K hZF hω ff' fg trace
      (fun i x hi => (orig i x hi).symm.trans (same i x hi)),
      ν, A, c, R, r, f, h, π, hν, hA, model, type, ff, fh, graph, cp, bij, perm⟩

/-- 同一个完整类型有恒等排列实例，所有赋值图均由原集合论构造。 -/
theorem ts_at_self_l {ω ν A c R n s δ U D w : M.Domain} (hω : M.IsOmega ω)
    (hA : V_d Q ν A) (model : Smem_d Q c A R) (type : Tt_realized_d Q ω c A R n s δ U D w) :
    Ts_at_d hZF ω δ n s n U D w ν := by
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) type.tuple) type.point
  obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
  obtain ⟨h, fh, graph⟩ := fn_recode_l Q K hZF (fn0_function_l (ZF.modelsKP hZF) type.tuple)
  have orig i x (hi : M.mem i n) : Rd_entry_d i x s ↔ M.PairMember K i x g :=
    (show Rd_entry_d i x s ↔ Rd_entry_d i x f from
      ⟨fun hx => (fill.2 i x).mpr ⟨hω.transitive hZF n type.finite i hi, Or.inl ⟨hi, hx⟩⟩,
        fun hx => ((fill.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)⟩).trans (agree i x).symm
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i j : φ.denote ρ i j ↔ j = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨π, fn, entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Q φ ρ (source := n) (target := n)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i j hi hj => ((sat i j).mp hj).symm ▸ hi)
  have id i j : Rd_entry_d i j π ↔ M.mem i n ∧ j = i := (entries i j).trans (and_congr_right fun _ => sat i j)
  have bij : M.IsSetBijectionFromTo Q π n n :=
    ⟨⟨fn, fun i j x hx hy => ((id i x).mp hx).2.symm.trans ((id j x).mp hy).2⟩,
      fun x hx => ⟨x, hx, (id x x).mpr ⟨hx, rfl⟩⟩⟩
  refine ⟨A, c, R, s, g, h, π, hA, model, type, fg, fh, graph, orig, bij, ?_⟩
  intro i hi x _
  refine ⟨fun hx => ⟨i, hi, (id i i).mpr ⟨hi, rfl⟩, (orig i x hi).mp ((graph i x).mp hx)⟩, ?_⟩
  rintro ⟨j, _, ij, jx⟩
  have eq := ((id i j).mp ij).2
  subst j
  exact (graph i x).mpr ((orig i x hi).mpr jx)

end YesMetaZFC.SetTheory.Internal

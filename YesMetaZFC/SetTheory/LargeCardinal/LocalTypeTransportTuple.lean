import YesMetaZFC.SetTheory.LargeCardinal.LocalTypeTransport
import YesMetaZFC.Model.SetTheory.Internal.TypeMoveQuote
import YesMetaZFC.SetTheory.CumulativeFinite

/-! # 已有完整类型的自动元组搬运接口

调用者给出实际秩层、元组和原 κ 型。整个共同参数带中的对象保持原值，
只替换出现的高度对象。参数带与指定常量 δ 独立，允许另行覆盖树的秩。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意内部有限元组均自动命名；原常量域、全部查询及完整类型集合字面不变。 -/
theorem Li_pair_d.transport_l {ω e γ W F δ ν μ κ k n β C A c R s B U D t : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) (hγ : M.IsLimitOrdinal γ)
    (hW : V_d Q γ W) (hδW : M.mem δ W) (pool₀ : Tt_pool_d Q ω e W F)
    (h : Li_pair_d Q ω e W F ν μ) (hκδ : M.mem κ δ) (hk : M.mem k ω) (hek : M.mem e k)
    (sum : M.IsOrdinalAddition Q β ν k) (hA : V_d Q β A) (model : Smem_d Q c A R)
    (hC : V_d Q δ C) (hB : V_d Q κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (type : Tt_realized_d Q ω c A R n s δ U D t)
    (values : ∀ i x, Rd_entry_d i x s → x = ν ∨ M.mem x W) :
    ∃ β' A' c' R' s', M.IsOrdinalAddition Q β' μ k ∧ V_d Q β' A' ∧ Smem_d Q c' A' R' ∧
      Tm_move_d ν μ s s' ∧ Tt_realized_d Q ω c' A' R' n s' δ U D t := by
  have hν := h.1
  have hμ := h.2.1
  have ho := hω.members_areOrdinals hZF k hk
  have wt := ZF.v_transitive_l Q hZF hW
  have hωW := wt δ hδW ω hωδ
  have hCW := ZF.v_mem_l Q hZF hC hW (ZF.v_ordinal_height_l hZF hW hδ.1 hδW)
  obtain ⟨β', sum', _⟩ := ZF.ordinalAddition_existsUnique hZF Q μ ho
  have hb' := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hμ).1.2 _ _ ho sum'
  obtain ⟨A', ha'⟩ := ZF.v_exists_l Q hZF hb'
  -- ν≤μ 推出 ν+k≤μ+k；这里只用加法余项、结合律和右参数单调性。
  have sub : M.MemberSubset A A' := by
    obtain ⟨j, add, _⟩ := ZF.ordinalAddition_existsUnique_rightRemainder hZF Q hν hμ h.2.2.1
    obtain ⟨l, plus, _⟩ := ZF.ordinalAddition_existsUnique hZF Q j ho
    have hj := add.right_isOrdinal
    have hl := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hj).1.2 _ _ ho plus
    obtain ⟨b, comb, _⟩ := ZF.ordinalAddition_existsUnique hZF Q ν hl
    have eq := ZF.ordinalAddition_assoc hZF Q hν hj ho add plus comb sum'
    have le : M.MemberSubset β β' := by
      rcases ZF.ordinalAddition_right_eq_or_mem hZF Q hj ho plus with eqk | lt
      · subst l
        obtain ⟨a, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF Q ν ho
        exact (unique β sum).trans ((unique b comb).symm.trans eq) ▸ (fun _ hx => hx)
      · exact hb'.transitive β (eq ▸ ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hν k l ho hl lt β b sum comb)
    exact ZF.v_mono_l Q hZF hA ha' le
  obtain ⟨N, names⟩ := tn_names_exists_l hZF e A
  obtain ⟨E, column, assign, quote, move⟩ := tm_quote_l hZF he names type.tuple
    (fun i x hx => Or.inr ((fn0_function_l (ZF.modelsKP hZF) type.tuple).output_mem_of_pairMember hx))
  -- 名字列的值全在共同参数带中；内部有限闭包给出列本身及一个源内名字界。
  have name_mem i a (ha : Rd_entry_d i a E) : M.mem a W := by
    obtain ⟨x, hx, ⟨_, eq⟩ | ⟨hne, code⟩⟩ := (quote i a).mp ha
    · exact eq.symm ▸ wt ω hωW e heω
    · have hxW := (values i x hx).resolve_left hne
      obtain ⟨P, hp, pair⟩ := sc_v_pair_l hZF hγ hW x x hxW hxW
      obtain ⟨Z, nz⟩ := tn_names_exists_l hZF e P
      exact wt Z (nz.rank_mem_l hZF hω hW hγ hωW heω hp) a
        ((nz a).mpr (Or.inr (Or.inr ⟨x, (pair x).mpr (Or.inl rfl), code⟩)))
  have ew := fn0_function_l (ZF.modelsKP hZF) (column.retarget_l name_mem)
  obtain ⟨Z, hZW, ez, hEW⟩ := ZF.v_finite_function_l hZF hω hγ hW hωW type.finite ew
  have empty : Fn0_d e A' e := ⟨fun p hp => (he p hp).elim,
    fun i hi => (he i hi).elim, fun i hi => (he i hi).elim⟩
  have hμβ' := (ZF.ordinalAddition_mem_iff hZF Q ho sum').mpr
    (Or.inr ⟨e, hek, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
  obtain ⟨s', assign', tuple'⟩ := tn_assign_exists_l hZF (Structure.IsOrdinal.of_no_members he) empty
    (ZF.v_ordinal_mem_l Q hZF ha' hμβ') sub names column
  have point' := sub δ type.point
  obtain ⟨c', R', model'⟩ := smdl_membership_l Q hZF ⟨δ, point'⟩
  have hUC := tt_constants_rank_l hZF hC hδ hκδ hB constants
  have hDC := type.pool.rank_mem_l hZF hω hC hδ (ZF.v_ordinal_mem_l Q hZF hC hωδ) type.finite hUC
  have htW := wt C hCW t (ZF.v_subset_mem_l Q hZF hC hDC (fun p hp => ((type.truth p).mp hp).1))
  have params : ∀ i, M.mem (tm_params_l ω C κ k n Z E δ e t i) W :=
    Fin.cases hωW (Fin.cases hCW (Fin.cases (wt δ hδW κ hκδ)
      (Fin.cases (wt ω hωW k hk) (Fin.cases (wt ω hωW n type.finite) (Fin.cases hZW
        (Fin.cases hEW (Fin.cases hδW (Fin.cases (wt ω hωW e heω) (fun _ => htW)))))))))
  obtain ⟨ξ, ζ, X, Y, a, H, b, K, u, sx, sy, hx, hy, mx, my, l, r, _⟩ := h.read_l hZF hω he heω pool₀
  have hξ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hν).limit_value (hω.isLimitOrdinal hZF) sx
  have hζ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hμ).limit_value (hω.isLimitOrdinal hZF) sy
  have hβξ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hν k ω ho (hω.isOrdinal hZF) hk β ξ sum sx
  have hβζ := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q hμ k ω ho (hω.isOrdinal hZF) hk β' ζ sum' sy
  have wb : M.MemberSubset ω β := fun i hi => (v_ordinal_l Q hA).transitive δ
    (ZF.v_ordinal_height_l hZF hA hδ.1 type.point) i (hδ.1.transitive ω hωδ i hi)
  have wb' : M.MemberSubset ω β' := fun i hi => hb'.transitive δ
    (ZF.v_ordinal_height_l hZF ha' hδ.1 point') i (hδ.1.transitive ω hωδ i hi)
  have low := l.move_read_l hZF mx hω hξ hx hν hk sum hβξ hA wb
    (ZF.v_transitive_l Q hZF hA δ type.point κ hκδ) hC hδ hωδ hκδ hB constants type.pool model type.finite
    (fn0_of_function_l (ZF.modelsKP hZF) ez) assign type.tuple type.point params
  have high := r.move_read_l hZF my hω hζ hy hμ hk sum' hβζ ha' wb'
    (ZF.v_transitive_l Q hZF ha' δ point' κ hκδ) hC hδ hωδ hκδ hB constants type.pool model' type.finite
    (fn0_of_function_l (ZF.modelsKP hZF) ez) assign' tuple' point' params
  have same := l.point_congr_l hZF hω r tm_type_f tm_type_closed_l (tm_params_l ω C κ k n Z E δ e t) params
  exact ⟨β', A', c', R', s', sum', ha', model', move μ s' assign',
    ⟨model'.1, type.finite, tuple', point', fun x hx => sub x (type.constants x hx), type.pool,
      high.mp (same.mp (low.mpr type.truth))⟩⟩

/-- 最小局部不可分辨对自动具备全部内部有限后继层的类型搬运实例。 -/
theorem li_canonical_finite_l {ω δ : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) :
    ∃ e γ W F ν μ C P Z, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ M.IsOrdinalAddition Q γ δ ω ∧
      V_d Q γ W ∧ Tt_pool_d Q ω e W F ∧ Li_least_d Q ω e W F δ ν μ ∧ V_d Q δ C ∧
      (∀ x, M.mem x P ↔ M.mem x C ∨ x = δ) ∧ Tn_names_d e P Z ∧
      ∀ κ k n E, M.mem κ δ → M.mem k ω → M.mem e k → M.mem n ω → Fn0_d n Z E →
        ∃ B U D t, V_d Q κ B ∧ (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧ Tt_pool_d Q ω n U D ∧
          Li_finite_d Q ω e δ ν k n E U D t ∧ Li_finite_d Q ω e δ μ k n E U D t := by
  obtain ⟨e, γ, W, F, ν, μ, he, heω, band, hw, pool, least⟩ := li_canonical_l Q hZF hω hδ.1
  obtain ⟨C, P, Z, hc, params, names, all⟩ :=
    least.2.1.finite_types_l hZF hω he heω hδ hωδ band hw pool least.1
  exact ⟨e, γ, W, F, ν, μ, C, P, Z, he, heω, band, hw, pool, least, hc, params, names, all⟩

/-- 参数带可取任意 θ≥δ；自动选出最小对后，直接搬运已有元组和原完整类型。 -/
theorem li_canonical_transport_l {ω δ θ : M.Domain} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ) (hθ : M.IsOrdinal θ) (hδθ : δ = θ ∨ M.mem δ θ) :
    ∃ e γ W F ν μ C, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ M.IsOrdinalAddition Q γ θ ω ∧
      V_d Q γ W ∧ Tt_pool_d Q ω e W F ∧ Li_least_d Q ω e W F θ ν μ ∧ V_d Q δ C ∧
      ∀ κ k n β A c R s B U D t, M.mem κ δ → M.mem k ω → M.mem e k →
        M.IsOrdinalAddition Q β ν k → V_d Q β A → Smem_d Q c A R → V_d Q κ B →
        (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) → Tt_realized_d Q ω c A R n s δ U D t →
        (∀ i x, Rd_entry_d i x s → x = ν ∨ M.mem x W) →
        ∃ β' A' c' R' s', M.IsOrdinalAddition Q β' μ k ∧ V_d Q β' A' ∧ Smem_d Q c' A' R' ∧
          Tm_move_d ν μ s s' ∧ Tt_realized_d Q ω c' A' R' n s' δ U D t := by
  obtain ⟨e, γ, W, F, ν, μ, he, heω, band, hw, pool, least⟩ := li_canonical_l Q hZF hω hθ
  have hγ := (ZF.ordinalAddition_isNormalOrdinalFunction hZF Q hθ).limit_value (hω.isLimitOrdinal hZF) band
  have hθγ := (ZF.ordinalAddition_mem_iff hZF Q (hω.isOrdinal hZF) band).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF Q he).mpr rfl⟩)
  have hδγ := hδθ.elim (fun eq => eq.symm ▸ hθγ) (hγ.1.transitive θ hθγ δ)
  obtain ⟨C, hc⟩ := ZF.v_exists_l Q hZF hδ.1
  refine ⟨e, γ, W, F, ν, μ, C, he, heω, band, hw, pool, least, hc,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hκδ hk hek sum ha model hb constants type values => ?_⟩
  exact least.2.1.transport_l hZF hω he heω hδ hωδ hγ hw (ZF.v_ordinal_mem_l Q hZF hw hδγ)
    pool hκδ hk hek sum ha model hc hb constants type values

end YesMetaZFC.SetTheory.LargeCardinal

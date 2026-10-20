import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource

/-! # 给定传递地模型的有限读写闭性

全部背景内部有限图先由配对、并集和内部自然数归纳回收，再读取地模型
自己的函数空间。因此不会把地模型内部的幂集当作背景的完整幂集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
  (ground : (rt_model_l X nx).Models ZF)
include hZF hX ground

/-- 传递 ZF 地模型的自然数集就是背景自然数集，无须外加 ω 正确性。 -/
theorem fs_omega_relative_l (ω : (rt_model_l X nx).Domain) (localω : (rt_model_l X nx).IsOmega ω) :
    M.IsOmega ω.val := by
  have limit := (rt_limit_l hX nx (ZF.modelsKP hZF) ω).mp (localω.isLimitOrdinal ground)
  obtain ⟨w, hw⟩ := ZF.exists_omega hZF
  rcases (hw.isOrdinal hZF).trichotomy hZF.1 limit.1 (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) w ω.val) with eq | lt | gt
  · exact hZF.1.eq_of_same_members w ω.val eq ▸ hw
  · let v : (rt_model_l X nx).Domain := ⟨w, hX ω.val ω.property w lt⟩
    have hv := rt_omega_l hX nx hZF.1 v hw
    have eq := ground.1.eq_of_same_members v ω (fun x => ⟨hv.2 ω localω.1 x, localω.2 v hv.1 x⟩)
    exact congrArg Subtype.val eq ▸ hw
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω.val (hw.subset_limitOrdinal hZF limit ω.val gt)).elim

theorem fs_read_relative_l (ω : (rt_model_l X nx).Domain) (hω : M.IsOmega ω.val) :
    Fs_read_d ω.val X := by
  have pair a b (ha : M.mem a X) (hb : M.mem b X) : ∃ p, M.mem p X ∧ Pair_d M p a b := by
    obtain ⟨p, code⟩ := KP.exists_pair (ZF.modelsKP ground) ⟨a, ha⟩ ⟨b, hb⟩
    let ρ : Env (rt_model_l X nx) 3 := ⟨Fin.cases p (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩)), fun _ => ω⟩
    exact ⟨p.val, p.property, (pair0_sat_l hZF.1 _ .newest (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l hX nx (pair0_delta_l ..) ρ).mp
        ((pair0_sat_l ground.1 ρ .newest (.bound 1) (.bound 2)).mpr code))⟩
  have un a (ha : M.mem a X) : ∃ p, M.mem p X ∧ M.IsUnionOf p a := by
    obtain ⟨p, code⟩ := KP.exists_union (ZF.modelsKP ground) ⟨a, ha⟩
    exact ⟨p.val, p.property, (rt_union_l hX nx p ⟨a, ha⟩).mp code⟩
  have finite {n A f} := sc_finite_function_l hZF (A := A) (n := n) (f := f) hω hX pair un ω.property
  refine ⟨hX, ω.property, pair, fun _ _ _ hn hA hf => finite hA hn hf, fun A n hA hn => ?_⟩
  let a : (rt_model_l X nx).Domain := ⟨A, hA⟩
  let m : (rt_model_l X nx).Domain := ⟨n, hX ω.val ω.property n hn⟩
  obtain ⟨D, space⟩ := ZF.exists_functionSpace ground (kp_pair_l (ZF.modelsKP ground)) m a
  refine ⟨D.val, D.property, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · exact (rt_fn_l hX nx hZF.1 m a ⟨f, hX D.val D.property f hf⟩).mp
      (fn0_of_function_l (ZF.modelsKP ground) ((space ⟨f, hX D.val D.property f hf⟩).mp hf))
  · let g : (rt_model_l X nx).Domain := ⟨f, finite (hX A hA) hn hf⟩
    exact (space g).mpr (fn0_function_l (ZF.modelsKP ground) ((rt_fn_l hX nx hZF.1 m a g).mpr hf))

theorem fs_rank_relative_l (ω : (rt_model_l X nx).Domain) (hω : M.IsOmega ω.val)
    {α V : M.Domain} (hV : M.mem V X) (rank : Vr_d X α V)
    (limit : M.IsLimitOrdinal α) (above : M.mem ω.val V) : Fs_read_d ω.val V := by
  apply (fs_read_relative_l hZF hX nx ground ω hω).rank_l hZF hω _ hV rank limit above
  intro a ha
  obtain ⟨p, code⟩ := KP.exists_union (ZF.modelsKP ground) ⟨a, ha⟩
  exact ⟨p.val, p.property, (rt_union_l hX nx p ⟨a, ha⟩).mp code⟩

end YesMetaZFC.SetTheory.LargeCardinal

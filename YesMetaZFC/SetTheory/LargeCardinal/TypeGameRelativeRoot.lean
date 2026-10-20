import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRelativeContext
import YesMetaZFC.Model.SetTheory.Internal.RelationSmall
import YesMetaZFC.Model.SetTheory.Internal.RelationHierarchy
import YesMetaZFC.Model.SetTheory.Internal.RelationLayer

/-! # 给定根上的恒等图和共同低层实现

根载体就是给定 X。实现图是根恒等图在反射层上的实际限制；它覆盖该层的
全部成员和全部前驱，并满足后继构造已有的内在秩、小性及子集闭包条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.root_relative_l {ω c X R η C : M.Domain} (context : Tg_context_d ω X η C)
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (small : Sc_small_d X C) (model : Smem_d I c X R) :
    ∃ π k, Smap_d I ω c c X X π ∧
      (∀ x, M.mem x X → Rd_entry_d x x π) ∧ Rr_layer_d I C X R C k ∧
      Rr_closed_d I X R C ∧ Rr_small_d I X R C ∧ Rr_rank_d I X R η C := by
  obtain ⟨π, embed, spec⟩ := smap_identity_l I hZF (c := c) (X := X) hω
  have fixed x (hx : M.mem x X) := (spec x x).mpr ⟨hx, rfl⟩
  have ct := context.rank.transitive_l hZF hX context.member
  obtain ⟨k, layer, _⟩ := rr_layer_mem_l I hZF model hX context.member ct
  refine ⟨π, k, embed, fixed, layer,
    embed.subsets_raw_l I hZF hω hX model model.1 (fixed C context.member)
      (fun _ _ ha hb sub => context.rank.subset_mem_l hX context.member ha hb sub),
    embed.small_raw_l hZF hω hX model model.1 (fixed C context.member) ct small, ?_⟩
  · let nx : Nonempty {x // M.mem x X} := ⟨⟨η, context.height⟩⟩
    let ρ : Env (rt_model_l X nx) 2 := ⟨Fin.cases ⟨C, context.member⟩
      (fun _ => ⟨η, context.height⟩), fun _ => ⟨η, context.height⟩⟩
    exact ⟨context.height, context.member, (smem_formula_l I model nx _ ρ).mp
      ((vr_sat_l (ZF.modelsKP hZF) hX nx ρ (.bound 1) .newest).mpr context.rank)⟩

end YesMetaZFC.SetTheory.LargeCardinal

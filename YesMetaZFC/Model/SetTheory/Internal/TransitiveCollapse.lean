import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure
import YesMetaZFC.SetTheory.Collapse.RelationSyntax

/-! # 指定坍塌图在传递子源中的读取

每个坍塌值恰为原前驱值之集；不以背景良基性或另一张坍塌图代替原方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem rt_wc_graph_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z})
    (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
    (X R F : (rt_model_l Z nz).Domain) (h : Wc_graph_d X R F) : Wc_graph_d X.val R.val F.val := by
  have ent := rt_entry_l hZ nz hKP.1
  refine ⟨(rt_relation_l hKP hZ nz pair F).mp h.1, fun a x hax => ?_⟩
  have ax := rd_entry_transitive_l hZ F.property hax
  obtain ⟨ha, total, values⟩ := h.2 ⟨a, ax.1⟩ ⟨x, ax.2⟩ ((ent ..).mpr hax)
  refine ⟨ha, (fun b hb hba => ?_), fun y => ⟨?_, ?_⟩⟩
  · obtain ⟨y, hby⟩ := total ⟨b, hZ X.val X.property b hb⟩ hb ((ent ..).mpr hba)
    exact ⟨y.val, (ent ..).mp hby⟩
  · intro hy
    obtain ⟨b, hb, hba, hby⟩ := (values ⟨y, hZ x ax.2 y hy⟩).mp hy
    exact ⟨b.val, hb, (ent ..).mp hba, (ent ..).mp hby⟩
  · rintro ⟨b, hb, hba, hby⟩
    exact (values ⟨y, (rd_entry_transitive_l hZ F.property hby).2⟩).mpr
      ⟨⟨b, hZ X.val X.property b hb⟩, hb, (ent ..).mpr hba, (ent ..).mpr hby⟩

end YesMetaZFC.SetTheory.Internal

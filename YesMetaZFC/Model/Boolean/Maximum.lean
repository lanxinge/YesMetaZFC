import YesMetaZFC.Model.Boolean.Mixing
import YesMetaZFC.Model.Boolean.Refinement

/-! # 标准布尔宇宙的最大值原理

先按可取的布尔值作不交细化，再给每个细化系数选择一个名称见证并混合。
布尔值域是小类型，名称载体始终固定在 `Type (u+1)`。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

/-- 尊重布尔值等号的谓词，其存在量词值由一个实际名称取得。 -/
theorem maximum (p : BV_graph.{u, u} B → B)
    (h : ∀ G H, 𝔹.le (𝔹.meet (bv_eq 𝔹 G H) (p G)) (p H)) :
    ∃ G, p G = 𝔹.iSup p := by
  obtain ⟨q, hq, hd, hs⟩ := 𝔹.disjoint_refinement (fun b => ∃ G, p G = b)
  let I := {b : B // q b}
  have hw (i : I) : ∃ G, 𝔹.le i.1 (p G) := by
    obtain ⟨b, ⟨G, rfl⟩, hb⟩ := (hq i.1 i.2).2
    exact ⟨G, hb⟩
  obtain ⟨F, hF⟩ := Classical.axiomOfChoice hw
  let w (i : I) := i.1
  have hd' (i j : I) (hne : i ≠ j) : 𝔹.meet (w i) (w j) = 𝔹.bot :=
    hd i.1 j.1 i.2 j.2 (fun he => hne (Subtype.ext he))
  refine ⟨mix 𝔹 F w, 𝔹.le_antisymm (𝔹.le_iSup p (mix 𝔹 F w)) ?_⟩
  change 𝔹.le (𝔹.sup (fun b => ∃ G, p G = b)) _
  rw [← hs]
  apply (𝔹.sup_le_iff _ _).mpr
  intro b hb
  let i : I := ⟨b, hb⟩
  have he : 𝔹.le b (bv_eq 𝔹 (F i) (mix 𝔹 F w)) := by
    rw [eq_symm]
    exact mix_eq 𝔹 F w hd' i
  exact 𝔹.le_trans (𝔹.le_meet he (hF i)) (h (F i) (mix 𝔹 F w))

end YesMetaZFC.Model.Boolean.BV_graph

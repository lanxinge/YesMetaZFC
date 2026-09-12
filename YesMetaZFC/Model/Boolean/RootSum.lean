import YesMetaZFC.Model.Boolean.Equality

/-! # 带权小图族的有根并合

复用原小图并合的节点、边与良基性。标签中的类型相等由命题指标的上确界处理，
构造不要求小指标域可判等，也不选择商代表。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u v w
variable {B : Type v} {ι : Type u}

def sum_val (R : Sup_order B) (F : ι → BV_graph.{u, v} B) (w : ι → B) :
    Option (Σ i, (F i).Domain) → Option (Σ i, (F i).Domain) → B
  | some ⟨i, a⟩, none => R.iSup (fun _ : a = (F i).root => w i)
  | some ⟨i, a⟩, some ⟨j, b⟩ => R.iSup (fun h : i = j => (F j).val (h ▸ a) b)
  | none, _ => R.bot

def root_sum (R : Sup_order B) (F : ι → BV_graph.{u, v} B) (w : ι → B) : BV_graph.{u, v} B where
  toWF_graph := SmallGraph.WF_graph.root_sum (fun i => (F i).toWF_graph)
  val := sum_val R F w

@[simp] theorem sum_val_root (R : Sup_order B) (F : ι → BV_graph.{u, v} B) (w : ι → B) (i : ι) :
    (root_sum R F w).val (some ⟨i, (F i).root⟩) none = w i := R.iSup_proof rfl _

@[simp] theorem sum_val_step (R : Sup_order B) (F : ι → BV_graph.{u, v} B) (w : ι → B)
    (i : ι) (a b : (F i).Domain) :
    (root_sum R F w).val (some ⟨i, a⟩) (some ⟨i, b⟩) = (F i).val a b := R.iSup_proof rfl _

variable (𝔹 : CB_alg B)

theorem sum_at_eq (F : ι → BV_graph.{u, v} B) (w : ι → B) (i : ι) (a : (F i).Domain) :
    bv_eq 𝔹 ((F i).at_node a) ((root_sum 𝔹.toSup_order F w).at_node (some ⟨i, a⟩)) = 𝔹.top := by
  apply eq_of_map 𝔹 _ _ (fun b => some ⟨i, b⟩) rfl
  · intro b c h; exact SmallGraph.SG_graph.Sum_edge.step i h
  · intro b c _; exact sum_val_step 𝔹.toSup_order F w i b c
  · intro b c h
    obtain ⟨a, ha, hc⟩ := SmallGraph.SG_graph.sum_step (fun i => (F i).toSG_graph) h
    exact ⟨a, ha, hc.symm⟩

/-- 并合根的隶属值恰好是各分量名称的带权上确界。 -/
theorem sum_mem (F : ι → BV_graph.{u, v} B) (w : ι → B) (G : BV_graph.{w, v} B) :
    bv_mem 𝔹 G (root_sum 𝔹.toSup_order F w) =
      𝔹.iSup (fun i => 𝔹.meet (w i) (bv_eq 𝔹 G (F i))) := by
  apply 𝔹.le_antisymm
  · apply (𝔹.iSup_le_iff _ _).mpr
    rintro ⟨b, hb⟩
    change SmallGraph.SG_graph.Sum_edge (fun i => (F i).toSG_graph) b none at hb
    cases hb with
    | root i =>
        change 𝔹.le (𝔹.meet ((root_sum 𝔹.toSup_order F w).val (some ⟨i, (F i).root⟩) none)
          (bv_eq 𝔹 G ((root_sum 𝔹.toSup_order F w).at_node (some ⟨i, (F i).root⟩)))) _
        rw [sum_val_root, ← eq_congr_right 𝔹 G (F i) _ (sum_at_eq 𝔹 F w i (F i).root)]
        exact 𝔹.le_iSup (fun i => 𝔹.meet (w i) (bv_eq 𝔹 G (F i))) i
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro i
    have h := mem_intro 𝔹 G (root_sum 𝔹.toSup_order F w)
      ⟨some ⟨i, (F i).root⟩, SmallGraph.SG_graph.Sum_edge.root i⟩
    change 𝔹.le (𝔹.meet ((root_sum 𝔹.toSup_order F w).val (some ⟨i, (F i).root⟩) none)
      (bv_eq 𝔹 G ((root_sum 𝔹.toSup_order F w).at_node (some ⟨i, (F i).root⟩)))) _ at h
    rwa [sum_val_root, ← eq_congr_right 𝔹 G (F i) _ (sum_at_eq 𝔹 F w i (F i).root)] at h

end YesMetaZFC.Model.Boolean.BV_graph

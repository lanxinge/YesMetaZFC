import YesMetaZFC.SetTheory.Filter
import YesMetaZFC.Model.Boolean.Ultrafilter

/-! # 集合滤子的 Tarski 扩张

谓词幂集给出布尔代数，集合滤子直接转用通用布尔滤子扩张定理。
经典双重否定只出现在代数律的命题证明中；选择严格扩张的数据操作统一封装于
`Model.Boolean.Ultrafilter`。本定理仍是宿主层定理，不冒充内部 ZFC 的推导。
-/

namespace YesMetaZFC.SetTheory.Filter
open Model.Boolean
universe u

/-- 谓词幂集的布尔运算均为逐点逻辑运算。 -/
def powerset_l (A : Type u) : BA_alg (A → Prop) where
  le s t := ∀ x, s x → t x
  bot := fun _ => False
  le_refl _ _ := id
  le_trans h k x hx := k x (h x hx)
  le_antisymm h k := funext (fun x => propext ⟨h x, k x⟩)
  bot_le _ _ := False.elim
  meet s t := fun x => s x ∧ t x
  imp s t := fun x => s x → t x
  le_meet_iff _ _ _ := ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
    fun ⟨h, k⟩ x hx => ⟨h x hx, k x hx⟩⟩
  le_imp_iff _ _ _ := ⟨fun h x ⟨hx, hy⟩ => h x hx hy, fun h x hx hy => h x ⟨hx, hy⟩⟩
  double_neg _ := funext (fun _ => propext Classical.not_not)

def boolean_l {A : Type u} (F : Filter A) : Filter_l (powerset_l A) where
  mem := F.sets
  top_mem := F.upward F.univ_mem (fun _ _ h => h)
  upward h k := F.upward h (fun {x} hx => k x hx)
  meet_mem := by
    intro s t hs ht
    exact F.inter_mem hs ht

def set_l {A : Type u} (F : Filter_l (powerset_l A)) : Filter A where
  sets := F.mem
  univ_mem := F.upward F.top_mem (fun _ _ => True.intro)
  upward := by
    intro s t h k
    exact F.upward h (fun _ hx => k hx)
  inter_mem := by
    intro s t hs ht
    exact F.meet_mem hs ht

/-- 每个适当集合滤子都有超滤扩张；选择只在通用 Tarski 证明中使用。 -/
theorem tarski_filter_extension_l {A : Type u} (F : Filter A) (hF : Proper F) :
    ∃ U : Filter A, IsUltrafilter U ∧ Extends F U := by
  have hp : (boolean_l F).Proper_l := by
    change ¬ F.sets emptySet
    exact hF
  obtain ⟨U, hU, h⟩ := Filter_l.tarski_extension_l (boolean_l F) hp
  refine ⟨set_l U, ⟨?_, ?_⟩, ?_⟩
  · exact hU.1
  · intro G hG hP
    have hGU : U.Extends_l (boolean_l G) := fun s hs => hG s hs
    have hGP : (boolean_l G).Proper_l := by
      change ¬ G.sets emptySet
      exact hP
    exact hU.2 (boolean_l G) hGU hGP
  · exact h

end YesMetaZFC.SetTheory.Filter

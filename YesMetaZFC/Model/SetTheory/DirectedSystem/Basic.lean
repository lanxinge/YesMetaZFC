import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 集合编码的定向系统

`p : A → J` 给每个带标号元素所属的分量；`T` 同时存储全部过渡映射，
`R` 存储各分量的关系。这样所有指标、元素和映射都是对象模型内的集合。
过渡映射要求单射并保持、反映关系；不预设极限或其良基性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Di_order_d (J L : M.Domain) : Prop where
  refl : ∀ i, M.mem i J → Rd_entry_d i i L
  trans : ∀ i j k, Rd_entry_d i j L → Rd_entry_d j k L → Rd_entry_d i k L
  bound : ∀ i j, Rd_entry_d i j L → M.mem i J ∧ M.mem j J
  directed : ∀ i j, M.mem i J → M.mem j J →
    ∃ k, M.mem k J ∧ Rd_entry_d i k L ∧ Rd_entry_d j k L

structure Di_system_d (J L A p T R : M.Domain) : Prop where
  order : Di_order_d J L
  index : Fn0_d A J p
  bound : ∀ x y, Rd_entry_d x y T → M.mem x A ∧ M.mem y A
  forward : ∀ x y i j, Rd_entry_d x i p → Rd_entry_d y j p →
    Rd_entry_d x y T → Rd_entry_d i j L
  identity : ∀ x, M.mem x A → Rd_entry_d x x T
  comp : ∀ x y z, Rd_entry_d x y T → Rd_entry_d y z T → Rd_entry_d x z T
  total : ∀ x i j, Rd_entry_d x i p → Rd_entry_d i j L →
    ∃ y, Rd_entry_d y j p ∧ Rd_entry_d x y T
  unique : ∀ x y z j, Rd_entry_d y j p → Rd_entry_d z j p →
    Rd_entry_d x y T → Rd_entry_d x z T → y = z
  injective : ∀ x y z i, Rd_entry_d x i p → Rd_entry_d y i p →
    Rd_entry_d x z T → Rd_entry_d y z T → x = y
  locality : ∀ x y, Rd_entry_d x y R → ∃ i, Rd_entry_d x i p ∧ Rd_entry_d y i p
  relation : ∀ x y i u v j, Rd_entry_d x i p → Rd_entry_d y i p →
    Rd_entry_d u j p → Rd_entry_d v j p → Rd_entry_d x u T → Rd_entry_d y v T →
    (Rd_entry_d x y R ↔ Rd_entry_d u v R)

/-- 两个带标号元素在某个共同分量中成为同一个元素。 -/
def Di_eq_d (T x y : M.Domain) : Prop := ∃ z, Rd_entry_d x z T ∧ Rd_entry_d y z T

def di_eq_m {d} (T x y : Term d) : Formula 1 d := .existsE
  (.conj (rd_entry_m x.weaken .newest T.weaken) (rd_entry_m y.weaken .newest T.weaken))
derive_free_closed di_eq_m

theorem di_eq_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T x y : Term d) :
    Formula.satisfies ρ (di_eq_m T x y) ↔ Di_eq_d (T.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [di_eq_m, Di_eq_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 在同一未来分量中读取关系。见证的指标不必是最小上界。 -/
def Di_rel_d (p T R x y : M.Domain) : Prop := ∃ i u v,
  Rd_entry_d u i p ∧ Rd_entry_d v i p ∧ Rd_entry_d x u T ∧ Rd_entry_d y v T ∧ Rd_entry_d u v R

def di_rel_m {d} (p T R x y : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (rd_entry_m (.bound 1) (.bound 2) p.weaken.weaken.weaken) (.conj
    (rd_entry_m .newest (.bound 2) p.weaken.weaken.weaken) (.conj
      (rd_entry_m x.weaken.weaken.weaken (.bound 1) T.weaken.weaken.weaken) (.conj
        (rd_entry_m y.weaken.weaken.weaken .newest T.weaken.weaken.weaken)
        (rd_entry_m (.bound 1) .newest R.weaken.weaken.weaken)))))))
derive_free_closed di_rel_m

theorem di_rel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p T R x y : Term d) :
    Formula.satisfies ρ (di_rel_m p T R x y) ↔
      Di_rel_d (p.eval ρ) (T.eval ρ) (R.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [di_rel_m, Di_rel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Di_eq_d.symm_l {T x y : M.Domain} (h : Di_eq_d T x y) : Di_eq_d T y x :=
  h.imp fun _ hh => hh.symm

variable {J L A p T R : M.Domain} (h : Di_system_d J L A p T R)
include h

theorem Di_system_d.eq_refl_l {x} (hx : M.mem x A) : Di_eq_d T x x :=
  ⟨x, h.identity x hx, h.identity x hx⟩

/-- 任意两条过渡箭头可进一步移到同一指标。 -/
theorem Di_system_d.common_l {x y} (hx : M.mem x A) (hy : M.mem y A) :
    ∃ i u v, Rd_entry_d u i p ∧ Rd_entry_d v i p ∧ Rd_entry_d x u T ∧ Rd_entry_d y v T := by
  obtain ⟨i, hi, hxi⟩ := h.index.2.1 x hx
  obtain ⟨j, hj, hyj⟩ := h.index.2.1 y hy
  obtain ⟨k, _, hik, hjk⟩ := h.order.directed i j hi hj
  obtain ⟨u, hu, hxu⟩ := h.total x i k hxi hik
  obtain ⟨v, hv, hyv⟩ := h.total y j k hyj hjk
  exact ⟨k, u, v, hu, hv, hxu, hyv⟩

theorem Di_system_d.eq_trans_l {x y z} (he : Di_eq_d T x y) (hf : Di_eq_d T y z) : Di_eq_d T x z := by
  obtain ⟨a, hxa, hya⟩ := he
  obtain ⟨b, hyb, hzb⟩ := hf
  obtain ⟨i, u, v, hui, hvi, hau, hbv⟩ := h.common_l (h.bound x a hxa).2 (h.bound z b hzb).2
  have e := h.unique y u v i hui hvi (h.comp y a u hya hau) (h.comp y b v hyb hbv)
  exact ⟨u, h.comp x a u hxa hau, e.symm ▸ h.comp z b v hzb hbv⟩

theorem Di_system_d.eq_at_l {x y i} (hx : Rd_entry_d x i p) (hy : Rd_entry_d y i p) :
    Di_eq_d T x y ↔ x = y :=
  ⟨fun ⟨z, hxz, hyz⟩ => h.injective x y z i hx hy hxz hyz,
    fun e => e ▸ h.eq_refl_l (h.index.bound_l hx).1⟩

/-- 只要两代表已经移到同一分量，关系便可在那里读取，无须继续寻找见证。 -/
theorem Di_system_d.rel_at_l {x y u v i} (hu : Rd_entry_d u i p) (hv : Rd_entry_d v i p)
    (hxu : Rd_entry_d x u T) (hyv : Rd_entry_d y v T) : Di_rel_d p T R x y ↔ Rd_entry_d u v R := by
  refine ⟨?_, fun hr => ⟨i, u, v, hu, hv, hxu, hyv, hr⟩⟩
  rintro ⟨j, a, b, ha, hb, hxa, hyb, hab⟩
  obtain ⟨k, _, hik, hjk⟩ := h.order.directed i j (h.index.bound_l hu).2 (h.index.bound_l ha).2
  obtain ⟨u', hu', huu'⟩ := h.total u i k hu hik
  obtain ⟨v', hv', hvv'⟩ := h.total v i k hv hik
  obtain ⟨a', ha', haa'⟩ := h.total a j k ha hjk
  obtain ⟨b', hb', hbb'⟩ := h.total b j k hb hjk
  have eu := h.unique x a' u' k ha' hu' (h.comp x a a' hxa haa') (h.comp x u u' hxu huu')
  have ev := h.unique y b' v' k hb' hv' (h.comp y b b' hyb hbb') (h.comp y v v' hyv hvv')
  exact (h.relation u v i u' v' k hu hv hu' hv' huu' hvv').mpr
    (eu ▸ ev ▸ (h.relation a b j a' b' k ha hb ha' hb' haa' hbb').mp hab)

theorem Di_system_d.rel_move_l {x y u} (hxu : Rd_entry_d x u T) (hy : M.mem y A) :
    Di_rel_d p T R x y ↔ Di_rel_d p T R u y := by
  obtain ⟨i, v, w, hv, hw, huv, hyw⟩ := h.common_l (h.bound x u hxu).2 hy
  exact (h.rel_at_l hv hw (h.comp x u v hxu huv) hyw).trans (h.rel_at_l hv hw huv hyw).symm

theorem Di_system_d.rel_move_right_l {x y v} (hx : M.mem x A) (hyv : Rd_entry_d y v T) :
    Di_rel_d p T R x y ↔ Di_rel_d p T R x v := by
  obtain ⟨i, u, w, hu, hw, hxu, hvw⟩ := h.common_l hx (h.bound y v hyv).2
  exact (h.rel_at_l hu hw hxu (h.comp y v w hyv hvw)).trans (h.rel_at_l hu hw hxu hvw).symm

theorem Di_system_d.rel_congr_l {x y u v} (he : Di_eq_d T x u) (hf : Di_eq_d T y v) :
    Di_rel_d p T R x y ↔ Di_rel_d p T R u v := by
  obtain ⟨a, hxa, hua⟩ := he
  obtain ⟨b, hyb, hvb⟩ := hf
  have hy := (h.bound y b hyb).1
  have hu := (h.bound u a hua).1
  exact (h.rel_move_l hxa hy).trans ((h.rel_move_l hua hy).symm.trans
    ((h.rel_move_right_l hu hyb).trans (h.rel_move_right_l hu hvb).symm))

end YesMetaZFC.SetTheory.Internal

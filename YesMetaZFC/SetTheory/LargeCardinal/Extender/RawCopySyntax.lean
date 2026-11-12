import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 原关系复制的统一节点公式

节点的支撑沿所属图逐点复制，类代表沿父模型图复制，然后取目标原极限值。
公式中的每个分量和商均由实际 Er_class 读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_node_d (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q u E : M.Domain) : Prop :=
  ∃ a B a' B' v, KPair_d M u a B ∧
    Er_class_d I ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B' ∧
    KPair_d M v a' B' ∧ Rd_entry_d v E q

def er_node_m {n} (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q u E : Term n) : Formula 1 n := set[n] ⟪
  ∃ a B a' B' v, ⌜kpair_m⌝ₚ(⌜u⌝ₛ, a, B) ∧
    ⌜er_class_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜F⌝ₛ, ⌜z⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜k⌝ₛ,
      ⌜L'⌝ₛ, ⌜N'⌝ₛ, ⌜T'⌝ₛ, ⌜ξ'⌝ₛ, ⌜F'⌝ₛ, ⌜z'⌝ₛ, ⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜k'⌝ₛ, ⌜π⌝ₛ, ⌜σ⌝ₛ, a, a', B, B') ∧
    ⌜kpair_m⌝ₚ(v, a', B') ∧ ⌜rd_entry0_m⌝ₚ(v, ⌜E⌝ₛ, ⌜q⌝ₛ)⟫

derive_free_closed er_node_m

theorem er_node_sat_l (ext : Extensional M) {n} (ρ : Env M n)
    (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q u E : Term n) :
    Formula.satisfies ρ (er_node_m ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q u E) ↔
      Er_node_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (F.eval ρ) (z.eval ρ)
        (X.eval ρ) (R.eval ρ) (k.eval ρ) (L'.eval ρ) (N'.eval ρ) (T'.eval ρ) (ξ'.eval ρ) (F'.eval ρ) (z'.eval ρ)
        (Y.eval ρ) (S.eval ρ) (k'.eval ρ) (π.eval ρ) (σ.eval ρ) (q.eval ρ) (u.eval ρ) (E.eval ρ) := by
  simp only [er_node_m, Er_node_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M ext, er_class_sat_l I ext, rd_entry0_sat_l ext, Definitional.Term.eval_weaken]; rfl

/-- 支撑坐标经实际分量投影和极限投影得到的值。 -/
def Er_seed_d (ω L N T ξ F z X R k q a E : M.Domain) : Prop :=
  ∃ o n m b d u D i t y V G p C W B v,
    Er_frame_d I ω L N T ξ F z X R k a o n m b d u D i t y V G p C W ∧
    Rd_entry_d t B p ∧ KPair_d M v a B ∧ Rd_entry_d v E q

def er_seed_m {n} (ω L N T ξ F z X R k q a E : Term n) : Formula 1 n := set[n] ⟪
  ∃ o n m b d u D i t y V G p C W B v,
    ⌜er_frame_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜F⌝ₛ, ⌜z⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜k⌝ₛ,
      ⌜a⌝ₛ, o, n, m, b, d, u, D, i, t, y, V, G, p, C, W) ∧
    ⌜rd_entry0_m⌝ₚ(t, B, p) ∧ ⌜kpair_m⌝ₚ(v, ⌜a⌝ₛ, B) ∧ ⌜rd_entry0_m⌝ₚ(v, ⌜E⌝ₛ, ⌜q⌝ₛ)⟫

derive_free_closed er_seed_m

theorem er_seed_sat_l (ext : Extensional M) {n} (ρ : Env M n) (ω L N T ξ F z X R k q a E : Term n) :
    Formula.satisfies ρ (er_seed_m ω L N T ξ F z X R k q a E) ↔
      Er_seed_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (F.eval ρ) (z.eval ρ)
        (X.eval ρ) (R.eval ρ) (k.eval ρ) (q.eval ρ) (a.eval ρ) (E.eval ρ) := by
  simp only [er_seed_m, Er_seed_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    er_frame_sat_l I ext, kpair_sat_l M ext, rd_entry0_sat_l ext, Definitional.Term.eval_weaken]; rfl

/-- 同一对原关系极限上的复制；常值方块也适用于原先给定的实际活动边。 -/
def Er_limit_d (hZF : M.Models ZF)
    (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q q' h h' o C U o' C' U' : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ τ i i', Smap_d I ω o o' C C' τ ∧ Smap_d I ω h o X C i ∧ Smap_d I ω h' o' Y C' i' ∧
    Er_constants_d X q i ∧ Er_constants_d Y q' i' ∧
    (∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧
      Er_node_d I ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q' u E) ∧
    (∀ x x' B E, Rd_entry_d x x' π → Rd_entry_d x B i → (Rd_entry_d B E τ ↔ Rd_entry_d x' E i')) ∧
    (∀ s s', Fn0_d X C s → Fn0_d Y C' s' → Er_constants_d X q s → Er_constants_d Y q' s' →
      ∀ x x' B E, Rd_entry_d x x' π → Rd_entry_d x B s → (Rd_entry_d B E τ ↔ Rd_entry_d x' E s')) ∧
    (∀ s, Fn0_d C C' s → (∀ u B E, Rd_entry_d u B q →
      Er_node_d I ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ q' u E → Rd_entry_d B E s) → s = τ) ∧
    (Wf_rel_d C' U' → Wf_rel_d C U) ∧
    (∀ a a' n B E, Fn0_d n L a → Fn0_d n L' a' → Smap_assign_d I n σ a a' →
      Er_seed_d I ω L N T ξ F z X R k q a B → Er_seed_d I ω L' N' T' ξ' F' z' Y S k' q' a' E →
        Rd_entry_d B E τ)

end YesMetaZFC.SetTheory.LargeCardinal

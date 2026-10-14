import YesMetaZFC.SetTheory.LargeCardinal.IterationConePull
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddRecords

/-! # 奇数边上的三张坐标图在返回极限中相容

继续边严格使用被原请求选中的完整存档。三张图的嵌入像均包含于新图，
故在同一返回锥中的像也满足包含；空标签仍保留原重置分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_odd_compatible_d (ω H G π P : M.Domain) : Prop := ∀ ξ α k e t ℓ Sₑ S n s g,
  Tg_odd_d ω H ξ α k G e t ℓ Sₑ S n s g → (t = e ∧ k = ξ ∧ g = e) ∨
    ∃ Y R μ K η C L V q S₀ n₀ s₀ t₀ g₀,
      Tg_past_at_d H ℓ k Y R μ K η C L V q ∧ Tg_saved_branch_d ω V q S₀ n₀ s₀ t₀ g₀ ∧
      M.mem n₀ ω ∧ M.SuccessorOf n n₀ ∧
      ∀ (i : Fin 3) a b p q x y, Rd_entry_d a ([s₀,t₀,g₀].get i) π → Rd_entry_d b ([s,t,g].get i) π →
        Rd_entry_d k p P → Rd_entry_d α q P → Rd_entry_d a x p → Rd_entry_d b y q → M.MemberSubset x y

theorem It_pull_subset_d.odd_l (hZF : M.Models ZF) {ω H T Q G π P : M.Domain}
    (h : It_pull_subset_d G π P) (hw : M.IsOmega ω) (diagram : It_diagram_d hZF ω ω T Q G)
    (models : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R ∧ M.TransitiveSet X)
    (links : Tg_past_links_d (kp_pair_l (ZF.modelsKP hZF)) H Q)
    (saved : ∀ m i Y R μ K η C L V q, Tg_past_at_d H m i Y R μ K η C L V q →
      Tg_saved_d hZF ω Y R μ K η C L V q) :
    Tg_odd_compatible_d ω H G π P := by
  intro ξ α k e t ℓ Sₑ S n s g odd
  rcases odd with reset | ⟨_, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, a, b, z, row, branch,
    hj, _, hn, hga, succ, _, graph, is, ss, it, st⟩
  · exact Or.inl ⟨reset.1, reset.2.1, reset.2.2.1⟩
  · have old := saved _ _ _ _ _ _ _ _ _ _ _ row
    have hb := branch
    obtain ⟨v, code, _, num, _⟩ := hb
    have finite : M.mem n₀ ω := num ▸ (old.node_l hZF code).1
    obtain ⟨c, hc, mc⟩ := links _ _ _ _ _ _ _ _ _ _ _ row
    have bound := diagram.order.bound k α (diagram.map_bound_l hZF hj)
    obtain ⟨d, hd⟩ := (diagram.model_domain α).mp bound.2
    obtain ⟨X, R', mx, xt⟩ := models α d hd
    have emb := diagram.elementary k α j c Y R d X R' hj hc hd mc.1 mx.1
    have fixed := emb.natural_l hZF hw old.source.source.transitive xt mc mx old.source.source.omega_mem n₀ finite
    have eq := emb.1.1.1.2 n₀ b n₀ hn fixed
    subst b
    refine Or.inr ⟨Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, row, branch, finite, succ, ?_⟩
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) i <;>
      intro x y p q u v hx hy hp hq hu hv
    · exact h k α j x s₀ y s s₀ p q u v hj hx hy is ss hp hq hu hv
    · exact h k α j x t₀ y t t₀ p q u v hj hx hy it st hp hq hu hv
    · exact h k α j x g₀ y g a p q u v hj hx hy hga (fun z hz => (graph z).mpr (Or.inl hz)) hp hq hu hv

end YesMetaZFC.SetTheory.LargeCardinal

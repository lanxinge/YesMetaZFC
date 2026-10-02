import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaKernelJoin
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaEnvelopeLink
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketNumeric
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectRawTreeBounds

/-! # 实际 ZFC 两种模式证书包的端到端计算规格 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
set_option autoImplicit false

def entries : List (Nat × SchemaTemplate.Kind) := [(8, .separation), (9, .collection)]

def runBranch (tag : Nat) (kind : SchemaTemplate.Kind) (packet : Nat) : Option Tree := do
  let input ← NatPacket.decode packet
  let (count, body) ← SchemaEnvelope.decode tag input
  SchemaKernelJoin.run kind count body

theorem branch_spec (tag : Nat) (kind : SchemaTemplate.Kind) (packet : Nat) (output : Tree) :
    runBranch tag kind packet = some output ↔ ∃ count body,
      NatPacket.decode packet = some (.node tag [leaf count, body]) ∧
      SchemaKernelJoin.run kind count body = some output := by
  constructor
  · intro h
    obtain ⟨input, hPacket, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨count, body⟩, hEnvelope, hOutput⟩ := Option.bind_eq_some_iff.mp hRest
    rw [(SchemaEnvelope.decode_eq_some_iff tag count input body).mp hEnvelope] at hPacket
    exact ⟨count, body, hPacket, hOutput⟩
  · rintro ⟨count, body, hPacket, hOutput⟩
    simp [runBranch, hPacket, SchemaEnvelope.decode, leaf, hOutput]

/-- 两个模式标签互斥；替换不被加入现有的 ZFC 公理表。 -/
def run (packet : Nat) : Option Tree :=
  (runBranch 8 .separation packet).orElse (fun _ => runBranch 9 .collection packet)

theorem run_of_branch (entry : Nat × SchemaTemplate.Kind) (hEntry : entry ∈ entries)
    (packet : Nat) (output : Tree) (h : runBranch entry.1 entry.2 packet = some output) :
    run packet = some output := by
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hEntry
  rcases hEntry with rfl | rfl
  · simp [run, h]
  · cases hFirst : runBranch 8 .separation packet with
    | none => simp [run, hFirst, h]
    | some first =>
      obtain ⟨n, body, hPacket, _⟩ := (branch_spec 8 .separation packet first).mp hFirst
      obtain ⟨m, other, hOther, _⟩ := (branch_spec 9 .collection packet output).mp h
      rw [hPacket] at hOther
      cases hOther

theorem run_spec (packet : Nat) (output : Tree) : run packet = some output ↔
    ∃ entry, entry ∈ entries ∧ runBranch entry.1 entry.2 packet = some output := by
  constructor
  · intro h
    cases hFirst : runBranch 8 .separation packet with
    | none => exact ⟨(9, .collection), by simp [entries] , by simpa [run, hFirst] using h⟩
    | some first =>
      have hEq : first = output := by simpa [run, hFirst] using h
      subst first
      exact ⟨(8, .separation), by simp [entries] , hFirst⟩
  · rintro ⟨entry, hEntry, hBranch⟩
    exact run_of_branch entry hEntry packet output hBranch

/-- 原树、参数数目和正文是仅有的三个外层见证。 -/
def witnesses (tag count : Nat) (body : Tree) : Fin 3 → Nat := fun i =>
  [treeValue (.node tag [leaf count, body]), count, treeValue body][i]

theorem witnesses_bound (tag count : Nat) (body : Tree) (i : Fin 3) :
    witnesses tag count body i < tableBoundValue (NatPacket.encode (.node tag [leaf count, body])) + 1 := by
  have hRaw := ObjectRawTreeBounds.packet_bound (.node tag [leaf count, body])
  have hCount := SchemaEnvelope.count_le tag count body
  have hBody := SchemaEnvelope.body_le tag count body
  have hAll := ObjectPacket.list_bounds
    [treeValue (.node tag [leaf count, body]), count, treeValue body]
    (tableBoundValue (NatPacket.encode (.node tag [leaf count, body]))) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
  exact Nat.lt_succ_of_le (hAll i)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaPacket

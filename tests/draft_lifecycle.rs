//! Integration tests for draft lifecycle with checkpoints and context trees.
//!
//! These tests verify the interaction between DraftBuffer, Checkpoint, and
//! ContextTree components for managing draft text in hierarchical scopes.

#[cfg(feature = "pathmap-backend")]
mod draft_lifecycle_tests {
    use liblevenshtein::contextual::{Checkpoint, CheckpointStack, ContextTree, DraftBuffer};

    #[test]
    fn test_basic_draft_checkpoint_workflow() {
        let mut buffer = DraftBuffer::new();
        let mut checkpoints = CheckpointStack::new();
    
        // Checkpoint empty state
        checkpoints.push_from_buffer(&buffer);
    
        // Type "hello"
        for ch in "hello".chars() {
            buffer.insert(ch);
        }
        assert_eq!(buffer.as_str(), "hello");
    
        // Checkpoint after "hello"
        checkpoints.push_from_buffer(&buffer);
    
        // Type " world"
        for ch in " world".chars() {
            buffer.insert(ch);
        }
        assert_eq!(buffer.as_str(), "hello world");
    
        // Undo to "hello"
        if let Some(checkpoint) = checkpoints.pop() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "hello");
    
        // Undo to empty
        if let Some(checkpoint) = checkpoints.pop() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "");
    }
    
    #[test]
    fn test_checkpoint_at_specific_positions() {
        let mut buffer = DraftBuffer::new();
    
        // Type "programming"
        for ch in "programming".chars() {
            buffer.insert(ch);
        }
    
        // Create checkpoints at different positions
        let checkpoint_5 = Checkpoint::at(5); // "progr"
        let checkpoint_7 = Checkpoint::at(7); // "program"
        let checkpoint_11 = Checkpoint::at(11); // "programming"
    
        // Restore to position 7
        checkpoint_7.restore(&mut buffer);
        assert_eq!(buffer.as_str(), "program");
    
        // Restore to position 5
        checkpoint_5.restore(&mut buffer);
        assert_eq!(buffer.as_str(), "progr");
    
        // Can't grow, but can restore to same length
        checkpoint_5.restore(&mut buffer);
        assert_eq!(buffer.as_str(), "progr");
    
        // Restore to longer position has no effect (can't grow with truncate)
        checkpoint_11.restore(&mut buffer);
        assert_eq!(buffer.as_str(), "progr"); // Still "progr"
    }
    
    #[test]
    fn test_context_tree_with_draft_lifecycle() {
        let mut tree = ContextTree::new();
        let mut buffers: std::collections::HashMap<u32, DraftBuffer> = std::collections::HashMap::new();
    
        // Create root context (global scope)
        let global_ctx = tree.create_root(0);
        buffers.insert(global_ctx, DraftBuffer::from_str("global_var"));
    
        // Create function context (child of global)
        let func_ctx = tree.create_child(1, global_ctx).unwrap();
        buffers.insert(func_ctx, DraftBuffer::from_str("local_var"));
    
        // Create block context (child of function)
        let block_ctx = tree.create_child(2, func_ctx).unwrap();
        buffers.insert(block_ctx, DraftBuffer::from_str("block_var"));
    
        // Verify hierarchy
        assert_eq!(tree.depth(global_ctx), Some(0));
        assert_eq!(tree.depth(func_ctx), Some(1));
        assert_eq!(tree.depth(block_ctx), Some(2));
    
        // Verify visible contexts from block
        let visible = tree.visible_contexts(block_ctx);
        assert_eq!(visible.len(), 3);
        assert!(visible.contains(&block_ctx));
        assert!(visible.contains(&func_ctx));
        assert!(visible.contains(&global_ctx));
    
        // Collect visible draft texts
        let mut visible_texts: Vec<String> = visible
            .iter()
            .filter_map(|ctx_id| buffers.get(ctx_id).map(|buf| buf.as_str()))
            .collect();
        visible_texts.sort(); // Make order deterministic for assertion
    
        assert_eq!(visible_texts, vec!["block_var", "global_var", "local_var"]);
    }
    
    #[test]
    fn test_multi_context_draft_management() {
        let mut tree = ContextTree::new();
        let mut drafts: std::collections::HashMap<u32, (DraftBuffer, CheckpointStack)> =
            std::collections::HashMap::new();
    
        // Create root context
        let root = tree.create_root(0);
        let mut root_buffer = DraftBuffer::new();
        let mut root_checkpoints = CheckpointStack::new();
    
        root_checkpoints.push_from_buffer(&root_buffer);
        for ch in "root".chars() {
            root_buffer.insert(ch);
        }
        root_checkpoints.push_from_buffer(&root_buffer);
    
        drafts.insert(root, (root_buffer, root_checkpoints));
    
        // Create two child contexts
        let child1 = tree.create_child(1, root).unwrap();
        let mut child1_buffer = DraftBuffer::new();
        let mut child1_checkpoints = CheckpointStack::new();
    
        child1_checkpoints.push_from_buffer(&child1_buffer);
        for ch in "child1".chars() {
            child1_buffer.insert(ch);
        }
        child1_checkpoints.push_from_buffer(&child1_buffer);
    
        drafts.insert(child1, (child1_buffer, child1_checkpoints));
    
        let child2 = tree.create_child(2, root).unwrap();
        let mut child2_buffer = DraftBuffer::new();
        let mut child2_checkpoints = CheckpointStack::new();
    
        child2_checkpoints.push_from_buffer(&child2_buffer);
        for ch in "child2".chars() {
            child2_buffer.insert(ch);
        }
        child2_checkpoints.push_from_buffer(&child2_buffer);
    
        drafts.insert(child2, (child2_buffer, child2_checkpoints));
    
        // Verify each context has its own draft
        assert_eq!(drafts.get(&root).unwrap().0.as_str(), "root");
        assert_eq!(drafts.get(&child1).unwrap().0.as_str(), "child1");
        assert_eq!(drafts.get(&child2).unwrap().0.as_str(), "child2");
    
        // Undo child1 to empty (pop current state, peek at previous)
        if let Some((buffer, checkpoints)) = drafts.get_mut(&child1) {
            checkpoints.pop(); // Pop the "child1" checkpoint
            if let Some(checkpoint) = checkpoints.peek() {
                checkpoint.restore(buffer); // Restore to empty checkpoint
            }
        }
        assert_eq!(drafts.get(&child1).unwrap().0.as_str(), "");
    
        // Other contexts unaffected
        assert_eq!(drafts.get(&root).unwrap().0.as_str(), "root");
        assert_eq!(drafts.get(&child2).unwrap().0.as_str(), "child2");
    }
    
    #[test]
    fn test_draft_discard_on_context_removal() {
        let mut tree = ContextTree::new();
        let mut drafts: std::collections::HashMap<u32, DraftBuffer> = std::collections::HashMap::new();
    
        // Create hierarchy: root -> func -> block
        let root = tree.create_root(0);
        drafts.insert(root, DraftBuffer::from_str("root"));
    
        let func = tree.create_child(1, root).unwrap();
        drafts.insert(func, DraftBuffer::from_str("func"));
    
        let block = tree.create_child(2, func).unwrap();
        drafts.insert(block, DraftBuffer::from_str("block"));
    
        // Verify all contexts exist
        assert_eq!(tree.len(), 3);
        assert_eq!(drafts.len(), 3);
    
        // Remove func context (and its descendants)
        assert!(tree.remove(func));
    
        // Only root context should remain in tree
        assert_eq!(tree.len(), 1);
    
        // Drafts are not auto-cleaned - they still exist until manually cleaned
        assert_eq!(drafts.len(), 3);
    
        // Clean up orphaned drafts (check if context still exists in tree)
        drafts.retain(|ctx_id, _| tree.depth(*ctx_id).is_some());
    
        // After cleanup, only root draft remains
        assert_eq!(drafts.len(), 1);
        assert!(drafts.contains_key(&root));
    }
    
    #[test]
    fn test_checkpoint_stack_capacity() {
        let mut buffer = DraftBuffer::new();
        let mut checkpoints = CheckpointStack::with_capacity(10);
    
        // Push 10 checkpoints
        for i in 0..10 {
            buffer.insert(char::from_digit(i, 10).unwrap());
            checkpoints.push_from_buffer(&buffer);
        }
    
        assert_eq!(checkpoints.len(), 10);
        assert_eq!(buffer.as_str(), "0123456789");
    
        // Pop all checkpoints and restore to each
        // Checkpoints are at positions 1, 2, 3, ..., 10
        for expected_len in (1..=10).rev() {
            let checkpoint = checkpoints.pop().unwrap();
            checkpoint.restore(&mut buffer);
            assert_eq!(buffer.len(), expected_len);
        }
    
        assert!(checkpoints.is_empty());
    }
    
    #[test]
    fn test_draft_finalization() {
        let mut buffer = DraftBuffer::new();
        let mut checkpoints = CheckpointStack::new();
    
        // Start with checkpoint
        checkpoints.push_from_buffer(&buffer);
    
        // Type draft text
        for ch in "draft_text".chars() {
            buffer.insert(ch);
        }
    
        // Finalize by extracting the text
        let finalized = buffer.as_str();
        assert_eq!(finalized, "draft_text");
    
        // Clear checkpoints since we're finalizing
        checkpoints.clear();
        assert!(checkpoints.is_empty());
    
        // Clear buffer for next draft
        buffer.clear();
        assert_eq!(buffer.as_str(), "");
    }
    
    #[test]
    fn test_draft_rollback_to_multiple_checkpoints() {
        let mut buffer = DraftBuffer::new();
        let mut checkpoints = CheckpointStack::new();
    
        // Checkpoint empty
        checkpoints.push_from_buffer(&buffer);
    
        // Type "a", checkpoint
        buffer.insert('a');
        checkpoints.push_from_buffer(&buffer);
    
        // Type "b", checkpoint
        buffer.insert('b');
        checkpoints.push_from_buffer(&buffer);
    
        // Type "c", checkpoint
        buffer.insert('c');
        checkpoints.push_from_buffer(&buffer);
    
        // Type "d", checkpoint
        buffer.insert('d');
        checkpoints.push_from_buffer(&buffer);
    
        assert_eq!(buffer.as_str(), "abcd");
        assert_eq!(checkpoints.len(), 5);
    
        // Rollback to "abc"
        checkpoints.pop();
        if let Some(checkpoint) = checkpoints.peek() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "abc");
    
        // Rollback to "ab"
        checkpoints.pop();
        if let Some(checkpoint) = checkpoints.peek() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "ab");
    
        // Rollback to "a"
        checkpoints.pop();
        if let Some(checkpoint) = checkpoints.peek() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "a");
    
        // Rollback to empty
        checkpoints.pop();
        if let Some(checkpoint) = checkpoints.peek() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "");
    }
    
    #[test]
    fn test_context_visibility_with_sibling_contexts() {
        let mut tree = ContextTree::new();
    
        // Create root
        let root = tree.create_root(0);
    
        // Create two sibling contexts
        let child1 = tree.create_child(1, root).unwrap();
        let child2 = tree.create_child(2, root).unwrap();
    
        // Create grandchild of child1
        let grandchild1 = tree.create_child(3, child1).unwrap();
    
        // Verify visibility from grandchild1
        let visible = tree.visible_contexts(grandchild1);
        assert_eq!(visible.len(), 3); // grandchild1, child1, root
        assert!(visible.contains(&grandchild1));
        assert!(visible.contains(&child1));
        assert!(visible.contains(&root));
        assert!(!visible.contains(&child2)); // Sibling not visible
    
        // Verify visibility from child2
        let visible = tree.visible_contexts(child2);
        assert_eq!(visible.len(), 2); // child2, root
        assert!(visible.contains(&child2));
        assert!(visible.contains(&root));
        assert!(!visible.contains(&child1)); // Sibling not visible
        assert!(!visible.contains(&grandchild1)); // Niece/nephew not visible
    }
    
    #[test]
    fn test_unicode_draft_with_checkpoints() {
        let mut buffer = DraftBuffer::new();
        let mut checkpoints = CheckpointStack::new();
    
        checkpoints.push_from_buffer(&buffer);
    
        // Type Unicode text: "Hello 世界"
        for ch in "Hello 世界".chars() {
            buffer.insert(ch);
        }
        assert_eq!(buffer.as_str(), "Hello 世界");
    
        checkpoints.push_from_buffer(&buffer);
    
        // Add emoji
        for ch in " 🌍".chars() {
            buffer.insert(ch);
        }
        assert_eq!(buffer.as_str(), "Hello 世界 🌍");
    
        checkpoints.push_from_buffer(&buffer);
    
        // Undo to "Hello 世界" (pop current, peek previous)
        checkpoints.pop(); // Remove "Hello 世界 🌍" checkpoint
        if let Some(checkpoint) = checkpoints.peek() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "Hello 世界");
    
        // Undo to empty (pop "Hello 世界", peek empty)
        checkpoints.pop();
        if let Some(checkpoint) = checkpoints.peek() {
            checkpoint.restore(&mut buffer);
        }
        assert_eq!(buffer.as_str(), "");
    }
}

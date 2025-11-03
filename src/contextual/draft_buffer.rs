//! Character-level draft buffer with rollback support.
//!
//! This module implements a buffer for tracking tentative text input with
//! efficient character-level insertion and deletion (backspace) operations.

use std::collections::VecDeque;

/// Buffer for managing draft text with character-level operations.
///
/// DraftBuffer uses a VecDeque to enable O(1) push/pop operations on both
/// ends, making it efficient for both forward typing and backspace operations.
///
/// # Memory Efficiency
///
/// - Small allocations: ~24 bytes base + character storage
/// - VecDeque growth: 2x when capacity exceeded (amortized O(1))
/// - No allocations for backspace (just decrements length)
///
/// # Use Cases
///
/// - Code editor: Track partial identifier as user types
/// - Autocomplete: Build query string incrementally
/// - Undo/redo: Checkpoint and restore buffer state
///
/// # Examples
///
/// ```
/// use liblevenshtein::contextual::DraftBuffer;
///
/// let mut buffer = DraftBuffer::new();
///
/// // User types "he"
/// buffer.insert('h');
/// buffer.insert('e');
/// assert_eq!(buffer.as_str(), "he");
///
/// // User types "l"
/// buffer.insert('l');
/// assert_eq!(buffer.as_str(), "hel");
///
/// // User hits backspace
/// assert_eq!(buffer.delete(), Some('l'));
/// assert_eq!(buffer.as_str(), "he");
/// ```
#[derive(Debug, Clone)]
pub struct DraftBuffer {
    /// Character storage (VecDeque for efficient push/pop on both ends)
    chars: VecDeque<char>,
}

impl DraftBuffer {
    /// Create a new empty draft buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let buffer = DraftBuffer::new();
    /// assert_eq!(buffer.len(), 0);
    /// assert!(buffer.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            chars: VecDeque::new(),
        }
    }

    /// Create a draft buffer with the given initial capacity.
    ///
    /// This avoids reallocation if you know the approximate size.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Initial capacity in characters
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// // Preallocate for typical identifier length
    /// let buffer = DraftBuffer::with_capacity(32);
    /// assert!(buffer.is_empty());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            chars: VecDeque::with_capacity(capacity),
        }
    }

    /// Create a draft buffer from an existing string.
    ///
    /// # Arguments
    ///
    /// * `s` - Initial string content
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let buffer = DraftBuffer::from_str("hello");
    /// assert_eq!(buffer.as_str(), "hello");
    /// assert_eq!(buffer.len(), 5);
    /// ```
    pub fn from_str(s: &str) -> Self {
        let chars: VecDeque<char> = s.chars().collect();
        Self { chars }
    }

    /// Insert a character at the end of the buffer.
    ///
    /// # Arguments
    ///
    /// * `ch` - Character to insert
    ///
    /// # Performance
    ///
    /// O(1) amortized. May trigger reallocation if capacity exceeded.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let mut buffer = DraftBuffer::new();
    /// buffer.insert('a');
    /// buffer.insert('b');
    /// assert_eq!(buffer.as_str(), "ab");
    /// ```
    pub fn insert(&mut self, ch: char) {
        self.chars.push_back(ch);
    }

    /// Delete the last character from the buffer (backspace).
    ///
    /// # Returns
    ///
    /// `Some(ch)` if a character was deleted, `None` if buffer was empty.
    ///
    /// # Performance
    ///
    /// O(1). No allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let mut buffer = DraftBuffer::from_str("test");
    /// assert_eq!(buffer.delete(), Some('t'));
    /// assert_eq!(buffer.delete(), Some('s'));
    /// assert_eq!(buffer.as_str(), "te");
    /// assert_eq!(buffer.len(), 2);
    /// ```
    pub fn delete(&mut self) -> Option<char> {
        self.chars.pop_back()
    }

    /// Get the buffer length in characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let buffer = DraftBuffer::from_str("hello");
    /// assert_eq!(buffer.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.chars.len()
    }

    /// Check if the buffer is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let buffer = DraftBuffer::new();
    /// assert!(buffer.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.chars.is_empty()
    }

    /// Get the buffer content as a string slice.
    ///
    /// # Performance
    ///
    /// O(n) allocation to collect characters into a String.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let buffer = DraftBuffer::from_str("test");
    /// assert_eq!(buffer.as_str(), "test");
    /// ```
    pub fn as_str(&self) -> String {
        self.chars.iter().collect()
    }

    /// Get the buffer content as a byte vector (UTF-8).
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let buffer = DraftBuffer::from_str("test");
    /// assert_eq!(buffer.as_bytes(), b"test");
    /// ```
    pub fn as_bytes(&self) -> Vec<u8> {
        self.as_str().into_bytes()
    }

    /// Clear all content from the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let mut buffer = DraftBuffer::from_str("test");
    /// buffer.clear();
    /// assert!(buffer.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.chars.clear();
    }

    /// Truncate the buffer to the specified length.
    ///
    /// If `len` is greater than the current length, this has no effect.
    ///
    /// # Arguments
    ///
    /// * `len` - Target length in characters
    ///
    /// # Examples
    ///
    /// ```
    /// use liblevenshtein::contextual::DraftBuffer;
    ///
    /// let mut buffer = DraftBuffer::from_str("hello");
    /// buffer.truncate(3);
    /// assert_eq!(buffer.as_str(), "hel");
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if len < self.chars.len() {
            self.chars.truncate(len);
        }
    }
}

impl Default for DraftBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl From<String> for DraftBuffer {
    fn from(s: String) -> Self {
        Self::from_str(&s)
    }
}

impl From<&str> for DraftBuffer {
    fn from(s: &str) -> Self {
        Self::from_str(s)
    }
}

impl std::fmt::Display for DraftBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let buffer = DraftBuffer::new();
        assert_eq!(buffer.len(), 0);
        assert!(buffer.is_empty());
        assert_eq!(buffer.as_str(), "");
    }

    #[test]
    fn test_insert() {
        let mut buffer = DraftBuffer::new();
        buffer.insert('a');
        buffer.insert('b');
        buffer.insert('c');
        assert_eq!(buffer.len(), 3);
        assert_eq!(buffer.as_str(), "abc");
    }

    #[test]
    fn test_delete() {
        let mut buffer = DraftBuffer::from_str("test");
        assert_eq!(buffer.delete(), Some('t'));
        assert_eq!(buffer.as_str(), "tes");
        assert_eq!(buffer.delete(), Some('s'));
        assert_eq!(buffer.as_str(), "te");
        assert_eq!(buffer.len(), 2);
    }

    #[test]
    fn test_delete_empty() {
        let mut buffer = DraftBuffer::new();
        assert_eq!(buffer.delete(), None);
    }

    #[test]
    fn test_from_str() {
        let buffer = DraftBuffer::from_str("hello");
        assert_eq!(buffer.len(), 5);
        assert_eq!(buffer.as_str(), "hello");
    }

    #[test]
    fn test_clear() {
        let mut buffer = DraftBuffer::from_str("test");
        buffer.clear();
        assert!(buffer.is_empty());
        assert_eq!(buffer.as_str(), "");
    }

    #[test]
    fn test_truncate() {
        let mut buffer = DraftBuffer::from_str("hello");
        buffer.truncate(3);
        assert_eq!(buffer.as_str(), "hel");
        assert_eq!(buffer.len(), 3);
    }

    #[test]
    fn test_truncate_longer() {
        let mut buffer = DraftBuffer::from_str("hi");
        buffer.truncate(10);
        assert_eq!(buffer.as_str(), "hi");
        assert_eq!(buffer.len(), 2);
    }

    #[test]
    fn test_unicode() {
        let mut buffer = DraftBuffer::new();
        buffer.insert('😀');
        buffer.insert('世');
        buffer.insert('界');
        assert_eq!(buffer.len(), 3);
        assert_eq!(buffer.as_str(), "😀世界");
        assert_eq!(buffer.delete(), Some('界'));
        assert_eq!(buffer.as_str(), "😀世");
    }

    #[test]
    fn test_as_bytes() {
        let buffer = DraftBuffer::from_str("test");
        assert_eq!(buffer.as_bytes(), b"test");
    }

    #[test]
    fn test_display() {
        let buffer = DraftBuffer::from_str("test");
        assert_eq!(format!("{}", buffer), "test");
    }

    #[test]
    fn test_from_string() {
        let buffer = DraftBuffer::from(String::from("hello"));
        assert_eq!(buffer.as_str(), "hello");
    }

    #[test]
    fn test_with_capacity() {
        let buffer = DraftBuffer::with_capacity(100);
        assert!(buffer.is_empty());
    }

    #[test]
    fn test_incremental_typing() {
        let mut buffer = DraftBuffer::new();

        // Simulate typing "hello"
        for ch in "hello".chars() {
            buffer.insert(ch);
        }
        assert_eq!(buffer.as_str(), "hello");

        // Simulate backspace twice
        buffer.delete();
        buffer.delete();
        assert_eq!(buffer.as_str(), "hel");

        // Continue typing "p"
        buffer.insert('p');
        assert_eq!(buffer.as_str(), "help");
    }
}
